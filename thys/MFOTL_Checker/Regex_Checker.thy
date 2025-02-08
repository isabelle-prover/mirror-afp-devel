(*<*)
theory Regex_Checker
imports Prelim Regex_Proof_Object
begin
(*>*)

context fixes test :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and testi :: "'b \<Rightarrow> nat" begin
fun rs_check where
  "rs_check (Regex.Skip n) (SSkip x y) = ((snd (rs_at testi (SSkip x y)) = x + n))"
| "rs_check (Regex.Test x) (STest y) = test x y"
| "rs_check (Regex.Plus r r') (SPlusL z) = rs_check r z"
| "rs_check (Regex.Plus r r') (SPlusR z) = rs_check r' z"
| "rs_check (Regex.Times r r') (STimes p1 p2) =
  (snd (rs_at testi p1) = fst (rs_at testi p2) \<and> rs_check r p1 \<and> rs_check r' p2)"
| "rs_check (Regex.Star r) (SStar_eps n) = True"
| "rs_check (Regex.Star r) (SStar ps) = (ps \<noteq> [] \<and>
    (\<forall>k \<in> {1 ..< length ps}. fst (rs_at testi (ps ! k)) = snd (rs_at testi (ps ! (k-1)))) \<and>
    (\<forall>k \<in> {0 ..< length ps}. fst (rs_at testi (ps ! k)) < snd (rs_at testi (ps ! k)) \<and> rs_check r (ps ! k)))"
| "rs_check _ _ = False"
end

lemma rs_check_cong[fundef_cong]:
  "p = p' \<Longrightarrow> (\<And>x sp. x \<in> regex.atms r \<Longrightarrow> sp \<in> spatms p \<Longrightarrow> t x sp = t' x sp)
\<Longrightarrow> (\<And>x. x \<in> spatms p \<Longrightarrow> ti x = ti' x) \<Longrightarrow> rs_check t ti r p = rs_check t' ti' r p'"
proof (hypsubst_thin, induct r p' rule: rs_check.induct)
  case (7 r ps)
  have "rs_check t ti r (ps ! k) = rs_check t' ti' r (ps ! k)" if "k \<in> {0 ..< length ps}" for k
    using that by (intro 7) (auto simp: Bex_def in_set_conv_nth)
  moreover have "rs_at ti (ps ! k) = rs_at ti' (ps ! k)" if "k \<in> {0 ..< length ps}" for k
    using that by (intro rs_at_cong 7) (auto simp: Bex_def in_set_conv_nth)
  ultimately show ?case
    by auto
qed(auto cong: rs_at_cong)

context fixes test :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and testi :: "'b \<Rightarrow> nat" begin
fun rv_check where
  "rv_check (Regex.Skip n) (VSkip i j) = (i \<le> j \<and> j \<noteq> i + n)"
| "rv_check (Regex.Test x) (VTest p) = test x p"
| "rv_check (Regex.Test x) (VTest_neq i j) = (i < j)"
| "rv_check (Regex.Plus r r') (VPlus p1 p2) = 
  (rv_check r p1 \<and> rv_check r' p2 \<and> rv_at testi p1 = rv_at testi p2)"
| "rv_check (Regex.Times r r') (VTimes ps) = (ps \<noteq> [] \<and>
    (\<exists>i j. i = fst (rv_at testi (snd (hd ps))) \<and> j = snd (rv_at testi (snd (last ps))) \<and>
    i + length ps - 1 = j \<and> (\<forall>k \<in> {0 ..< length ps}. let (b, p) = ps ! k in 
    if b then rv_check r p \<and> rv_at testi p = (i, i + k)
         else rv_check r' p \<and> rv_at testi p = (i + k, j))))"
| "rv_check (Regex.Star r) (VStar ps) =
  (\<exists>S T i j. S = set (map (fst \<circ> rv_at testi) ps) \<and> T = set (map (snd \<circ> rv_at testi) ps)
  \<and> i = Min S \<and> j = Max T \<and> i \<le> j \<and> S \<inter> T = {} \<and> S \<union> T = {i .. j}
  \<and> map (rv_at testi) ps = sorted_list_of_set (rm (S \<times> T))
  \<and> (\<forall>k \<in> {0 ..< length ps}. rv_check r (ps ! k)))"
| "rv_check (Regex.Star r) (VStar_gt n n') = (n > n')"
| "rv_check _ _ = False"

lemma rv_check_code_Times:
  "rv_check (Regex.Times r r') (VTimes ps) = (ps \<noteq> [] \<and>
    (let i = fst (rv_at testi (snd (hd ps))); j = snd (rv_at testi (snd (last ps))) in
    i + length ps - 1 = j \<and> (\<forall>k \<in> {0 ..< length ps}. let (b, p) = ps ! k in 
    if b then rv_check r p \<and> rv_at testi p = (i, i + k)
         else rv_check r' p \<and> rv_at testi p = (i + k, j))))"
  by (simp add: Let_def)
lemma rv_check_code_Star:
  "rv_check (Regex.Star r) (VStar ps) =
  (let S = set (map (fst \<circ> rv_at testi) ps); T = set (map (snd \<circ> rv_at testi) ps);
  i = Min S; j = Max T in i \<le> j \<and> S \<inter> T = {} \<and> S \<union> T = {i .. j}
  \<and> map (rv_at testi) ps = sorted_list_of_set (rm (S \<times> T))
  \<and> (\<forall>k \<in> {0 ..< length ps}. rv_check r (ps ! k)))"
  by (simp add: Let_def)

declare rv_check.simps[code del]
lemmas rv_check_code[code] = rv_check.simps(1-4) rv_check_code_Times rv_check_code_Star rv_check.simps(7-)
end

lemma rv_check_cong[fundef_cong]:
  "p = p' \<Longrightarrow> (\<And>x vp. x \<in> regex.atms r \<and> vp \<in> vpatms p \<Longrightarrow> t x vp = t' x vp)
\<Longrightarrow> (\<And>x. x \<in> vpatms p \<Longrightarrow> ti x = ti' x) \<Longrightarrow> rv_check t ti r p = rv_check t' ti' r p'"
proof (hypsubst_thin, induct r p' rule: rv_check.induct)
  case (5 r r' ps)
  have "rv_check t ti r (snd (ps ! k)) = rv_check t' ti' r (snd (ps ! k))" if "fst (ps ! k)" "k \<in> {0 ..< length ps}" for k
    using that surjective_pairing[of "ps ! k"]
    by (intro 5(1)[OF that(2) refl prod.collapse that(1)] 5(3-))
     (auto simp: Bex_def in_set_conv_nth  simp del: prod.collapse)
  moreover have "rv_check t ti r' (snd (ps ! k)) = rv_check t' ti' r' (snd (ps ! k))" if "\<not> fst (ps ! k)" "k \<in> {0 ..< length ps}" for k
    using that surjective_pairing[of "ps ! k"]
    by (intro 5(2)[OF that(2) refl prod.collapse that(1)] 5(3-))
     (auto simp: Bex_def in_set_conv_nth  simp del: prod.collapse)
  moreover have "rv_at ti (snd (ps ! k)) = rv_at ti' (snd (ps ! k))" if "k \<in> {0 ..< length ps}" for k
    using that surjective_pairing[of "ps ! k"] by (intro rv_at_cong 5 refl)
      (auto simp: Bex_def in_set_conv_nth simp del: prod.collapse)
  ultimately show ?case
    by (auto simp: hd_conv_nth last_conv_nth split_beta)
next
  case (6 r ps)
  have "rv_check t ti r  (ps ! k) = rv_check t' ti' r (ps ! k)" if "k \<in> {0 ..< length ps}" for k
    using that by (intro 6) (auto simp: Bex_def in_set_conv_nth)
  moreover have "map (rv_at ti) ps = map (rv_at ti') ps"
    by (intro rv_at_cong 6 list.map_cong) (auto simp: Bex_def in_set_conv_nth)
  ultimately show ?case unfolding rv_check.simps list.map_comp[symmetric]
    by metis
qed (auto cong: rv_at_cong)

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

lemma rs_check_sound:
  "\<forall>x \<in> Regex.atms r. \<forall>p' \<in> spatms p. test x p' \<longrightarrow> sat (testi p') x \<Longrightarrow>
  rs_check test testi r p \<Longrightarrow> Regex_Proof_System.SAT sat (fst (rs_at testi p)) (snd (rs_at testi p)) r"
proof (induction p arbitrary: r)
  case (SSkip x y)
  then show ?case
    by (cases r) (auto intro: SAT.SSkip)
next
  case (STest x)
  then show ?case
    by (cases r) (auto intro: SAT.STest)
next
  case (SPlusL p)
  then show ?case
    by (cases r) (auto intro: SAT.SPlusL)
next
  case (SPlusR p)
  then show ?case
    by (cases r) (auto intro: SAT.SPlusR)
next
  case (STimes p1 p2)
  then show ?case
    by (cases r) (auto intro!: SAT.STimes)
next
  case (SStar_eps x)
  then show ?case
    by (cases r) (auto intro: SAT.SStar_eps)
next
  case (SStar ps)
  then show ?case using SStar
  proof (cases r)
    case (Star r')
    then have ps_ne: "ps \<noteq> []" and
      ps_chain: "\<forall>k \<in> {1 ..< length ps}. fst (rs_at testi (ps ! k)) = snd (rs_at testi (ps ! (k-1)))"
      using SStar by auto
    
    define ts where "ts = map (fst o rs_at testi) ps @ [snd (rs_at testi (last ps))]"
    then have ts_len: "2 \<le> length ts" and ts_ne[simp]: "ts \<noteq> []"
      using ps_ne by (cases ps; auto)+

    from SStar(2) Star
    have r'_atms: "\<forall>y \<in> Regex.atms r'. \<forall>p' \<in> spatms (SStar ps). test y p' \<longrightarrow> sat (testi p') y"
      by auto

    { fix k
      assume k_def: "k \<in> {0 ..< length ps}"
      then have "Regex_Proof_System.SAT sat (fst (rs_at testi (ps ! k))) (snd (rs_at testi (ps ! k))) r' \<and>
        fst (rs_at testi (ps ! k)) < snd (rs_at testi (ps ! k))"
        using SStar(1)[of "ps ! k" r'] r'_atms SStar(2-3) Star by force
    }
    
    then have sat_props_ts: "\<forall>k \<in> {0 ..< length ts - 1}. ts ! k < ts ! Suc k \<and>
      Regex_Proof_System.SAT sat (ts ! k) (ts ! Suc k) r'"
      "hd ts = fst (rs_at testi (hd ps))" "last ts = snd (rs_at testi (last ps))"
      using ps_ne ps_chain
      by (auto simp: ts_def nth_append last_conv_nth neq_Nil_conv less_Suc_eq)
    then have s_ts: "sorted_wrt (<) ts"
      by (subst sorted_wrt_iff_nth_Suc_transp) auto
    have form: "\<exists>zs. ts = hd ts # zs @ [last ts]"
      using ts_len by (cases ts) (auto intro!: exI[of _ "butlast _"] append_butlast_last_id[symmetric])
    then have "hd ts < last ts"
      using s_ts form ts_len by (auto simp: sorted_wrt_iff_nth_less hd_conv_nth last_conv_nth)
    then show ?thesis using sat_props_ts form ts_def
        SAT.SStar[of "hd ts" "last ts" ts sat r'] Star by auto
  qed auto
qed

lemma rs_check_complete:
  "(\<forall>x \<in> Regex.atms r. \<forall>i. sat i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')) \<Longrightarrow>
  Regex_Proof_System.SAT sat i j r \<Longrightarrow> \<exists>p. rs_check test testi r p \<and> rs_at testi p = (i, j)"
proof(induction r arbitrary: i j)
  case (Skip x)
  then have j_eq_i_plus_x: "j = i + x"
    using SAT.simps[of sat i j "Regex.Skip x"]
    by simp
  then have "rs_check test testi (Regex.Skip x) (SSkip i x)"
    using rs_check.simps(1)[of test testi x i x]
    by simp
  then show ?case
    using j_eq_i_plus_x rs_at.simps(1)[of testi i x]
    by blast
next
  case (Test x)
  then have props: "i = j \<and> sat j x"
    using SAT.simps[of sat i j "Regex.Test x"]
    by auto
  then obtain p' where p'_def: "test x p' \<and> testi p' = j"
    using Test(1)
    by auto
  then show ?case
    using rs_check.simps(2)[of test testi x p'] props
      rs_at.simps(2)[of testi p']
    by blast
next
  case (Plus r1 r2)
  from Plus(4) have "Regex_Proof_System.SAT sat i j r1 \<or> Regex_Proof_System.SAT sat i j r2"
    using SAT.simps[of sat i j "Regex.Plus r1 r2"]
    by simp
  moreover
  {
    assume sl: "Regex_Proof_System.SAT sat i j r1"
    from Plus(3) have r1_atms: " \<forall>x\<in>regex.atms r1. \<forall>i. sat i x \<longrightarrow>
         (\<exists>p'. testi p' = i \<and> test x p')"
      by auto
    from Plus(1)[OF r1_atms sl]
    obtain p where p_check: "rs_check test testi r1 p"
      and p_at: "rs_at testi p = (i, j)"
      by auto
    then have "\<exists>p. rs_check test testi (Regex.Plus r1 r2) p \<and> rs_at testi p = (i, j)"
      using rs_check.simps(3)[of test testi r1 r2 p]
      by fastforce
  }
  moreover
  {
    assume sr: "Regex_Proof_System.SAT sat i j r2"
    from Plus(3) have r2_atms: " \<forall>x\<in>regex.atms r2. \<forall>i. sat i x \<longrightarrow>
         (\<exists>p'. testi p' = i \<and> test x p')"
      by auto
    from Plus(2)[OF r2_atms sr]
    obtain p where p_check: "rs_check test testi r2 p"
      and p_at: "rs_at testi p = (i, j)"
      by auto
    then have "\<exists>p. rs_check test testi (Regex.Plus r1 r2) p \<and> rs_at testi p = (i, j)"
      using rs_check.simps(4)[of test testi r1 r2 p]
      by fastforce
  }
  ultimately show ?case
    by auto
next
  case (Times r1 r2)
  then obtain k where ks_r1: "Regex_Proof_System.SAT sat i k r1"
    and ks_r2: "Regex_Proof_System.SAT sat k j r2"
    using SAT.simps[of sat i j "Regex.Times r1 r2"]
    by auto
  from Times(3) have r1_atms: "\<forall>x\<in>regex.atms r1. \<forall>i. sat i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')" and
    r2_atms: "\<forall>x\<in>regex.atms r2. \<forall>i. sat i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')"
    by auto
  from Times(1)[OF r1_atms ks_r1] obtain p where
    p_check: "rs_check test testi r1 p" and p_at: "rs_at testi p = (i, k)"
    by auto
  from Times(2)[OF r2_atms ks_r2] obtain p' where
    p'_check: "rs_check test testi r2 p'" and p'_at: "rs_at testi p' = (k, j)"
    by auto
  then show ?case
    using rs_check.simps(5)[of test testi r1 r2 p p'] p_check p_at
    by fastforce
next
  case (Star r')
  then show ?case
  proof (cases "i = j")
    case True
    then show ?thesis
      using rs_check.simps(6)[of test testi r'] rs_at.simps(6)
      by blast
  next
    case False
    then have i_less_j: "i < j"
      using Star SAT.simps[of sat i j "Regex.Star r'"]
      by simp
    from Star i_less_j SAT.simps[of sat i j "Regex.Star r'"]
    obtain xs and zs where xs_def: "xs = i # zs @ [j]" and
      k_less: "\<forall>k \<in> {0 ..< length xs - 1}. xs ! k < xs ! Suc k" and
      k_sat: "\<forall>k \<in> {0 ..< length xs - 1}. Regex_Proof_System.SAT sat (xs ! k) (xs ! Suc k) r'"
      by auto
    from Star(2) have r'_atms: "\<forall>x\<in>regex.atms r'. \<forall>i. sat i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')"
      by auto

    {fix k
      assume k_in: "k \<in> {0 ..< length xs - 1}"
      then have ksat: "Regex_Proof_System.SAT sat (xs ! k) (xs ! Suc k) r'"
        using k_sat
        by auto
      from Star(1)[OF r'_atms ksat]
      have "\<exists>p. rs_check test testi r' p \<and> rs_at testi p = (xs ! k, xs ! Suc k)"
        by simp
    } thm rs_check.simps(7)
    then have k_ex_p: "\<forall>k \<in> {0 ..< length xs - 1}. \<exists>p. rs_check test testi r' p \<and> rs_at testi p = (xs ! k, xs ! Suc k)"
      by auto
    then obtain f where f_def: "\<forall>k \<in> {0 ..< length xs - 1}. rs_at testi (f k) = (xs ! k, xs ! Suc k) \<and> rs_check test testi r' (f k)"
      using bchoice[OF k_ex_p]
      by atomize_elim auto
    define ps where "ps = map f [0 ..< length xs - 1]"
    then have ps_check_and_less: "\<forall>k \<in> {0 ..< length ps}. rs_check test testi r' (ps ! k) \<and> fst (rs_at testi (ps ! k)) < snd (rs_at testi (ps ! k))"
      using f_def k_less by auto
    moreover
    from ps_def f_def
    have k_eq_prev: "\<forall>k \<in> {1 ..< length ps}. fst (rs_at testi (ps ! k)) = snd (rs_at testi (ps ! (k - 1)))"
      by auto
    moreover
    from xs_def ps_def have ps_nnil: "ps \<noteq> []"
      by auto
    moreover
    from f_def have hd_eq: "fst (rs_at testi (hd ps)) = i"
      using ps_def ps_nnil upt_rec xs_def by auto
    moreover
    from xs_def ps_def f_def have last_eq: "snd (rs_at testi (last ps)) = j"
      using ps_nnil by auto
    ultimately show ?thesis
      by (auto intro!: exI[of _ "SStar ps"])
  qed
qed

lemma rv_check_sound:
  "\<forall>x \<in> Regex.atms r. \<forall>p' \<in> vpatms p. test x p' \<longrightarrow> vio (testi p') x \<Longrightarrow>
    rv_check test testi r p \<Longrightarrow> Regex_Proof_System.VIO vio (fst (rv_at testi p)) (snd (rv_at testi p)) r"
proof (induction p arbitrary: r)
  case (VSkip x y)
  then show ?case
    by (cases r) (auto intro: VIO.VSkip)
next
  case (VTest x)
  then show ?case
    by (cases r) (auto intro: VIO.VTest)
next
  case (VTest_neq x y)
  then show ?case
    by (cases r) (auto intro: VIO.VTest_neq)
next
  case (VPlus p1 p2)
  then show ?case
    by (cases r) (auto intro: VIO.VPlus)
next
  case (VTimes ps)
  then show ?case
  proof (cases r)
    case (Times r1 r2)
    then obtain i and j where ps_ne: "ps \<noteq> []" and i_def: "i = fst (rv_at testi (snd (hd ps)))" and
      j_def: "j = snd (rv_at testi (snd (last ps)))" and ij_props: "i + length ps - 1 = j"
      using VTimes(3) by simp
    then have k_props: "\<forall>k \<in> {0 ..< length ps}. if fst (ps ! k)
      then rv_check test testi r1 (snd (ps ! k)) \<and> rv_at testi (snd (ps ! k)) = (i, i + k)
      else rv_check test testi r2 (snd (ps ! k)) \<and> rv_at testi (snd (ps ! k)) = (i + k, j)"
      using VTimes(3) Times by auto
    from VTimes(2) Times have r1_atms: "\<forall>y \<in> Regex.atms r1. \<forall>p' \<in> vpatms (VTimes ps). test y p' \<longrightarrow> vio (testi p') y"
      by auto
    from VTimes(2) Times have r2_atms: "\<forall>y \<in> Regex.atms r2. \<forall>p' \<in> vpatms (VTimes ps). test y p' \<longrightarrow> vio (testi p') y"
      by auto

    { fix k
      assume k_def: "k \<in> {0 ..< length ps}"
      then have "if fst (ps ! k) then Regex_Proof_System.VIO vio i (i + k) r1 else Regex_Proof_System.VIO vio (i + k) j r2"
        using VTimes(1)[of "ps ! k" "snd (ps ! k)" r1] VTimes(1)[of "ps ! k" "snd (ps ! k)" r2] Times k_props r1_atms r2_atms
        by (fastforce simp: prod_set_defs)
    } note k_vio = this

    define ts where "ts = map (\<lambda>k. if fst (ps ! k) then
      snd (rv_at testi (snd (ps ! k))) else fst (rv_at testi (snd (ps ! k)))) [0 ..< length ps]"
    then have ts_ps: "length ts = length ps" and ts_ne[simp]: "ts \<noteq> []"
      using ps_ne by (cases ps; auto)+
      
    { fix k
      assume k_def: "k \<in> set ts"
      then obtain k' where k'_def: "k = i + k'" "k' \<in> {0 ..< length ps}"
        using k_def k_props unfolding ts_def by auto
      then have "if fst (ps ! (k - i)) then Regex_Proof_System.VIO vio i k r1 else Regex_Proof_System.VIO vio k j r2"
        using k'_def k_vio[of k'] by auto
    } note k_vio_ts = this

    { fix k
      assume k_def: "k \<in> set ts"
      with k_props ij_props have "k \<in> {i .. j}"
        unfolding ts_def by auto
    }
    moreover
    { fix k
      assume k_def: "k \<in> {i .. j}"
      then obtain n where "n < length ps" "i + n = k"
        using ij_props ps_ne by (auto simp: nat_le_iff_add neq_Nil_conv)
      then have "k = ts ! n"
        using k_def k_props unfolding ts_def by auto
      then have "k \<in> set ts" using \<open>n < length ps\<close> ts_ps
        by (auto simp: in_set_conv_nth)
    }
    ultimately have "set ts = {i .. j}" by blast
    then show ?thesis using k_vio_ts i_def j_def ps_ne
      VIO.VTimes[of i j vio r1 r2] Times unfolding rv_at.simps by (smt (verit, best) split_pairs)
  qed auto
next
  case (VStar ps)
  then show ?case
  proof (cases r)
    case (Star r')
    define S and T where "S = set (map (fst \<circ> rv_at testi) ps)"
      and "T = set (map (snd \<circ> rv_at testi) ps)"
    define i and j where "i = Min S" and "j = Max T"
    then have ST_props: "S \<inter> T = {}" "S \<union> T = {i .. j}" and i_le_j: "i \<le> j"
      using VStar Star S_def T_def by auto
    then have ST_not_empty: "S \<noteq> {}" "T \<noteq> {}" and ps_ne: "ps \<noteq> []"
      unfolding S_def T_def using i_le_j by auto
    then have prod_not_empty: "S \<times> T \<noteq> {}"
      by auto
    from ST_props have ST_finite: "finite S" "finite T"
      unfolding S_def T_def by auto
    then have i_in: "i \<in> S" and j_in: "j \<in> T"
      using Min_in[of S] Max_in[of T] ST_props ST_not_empty unfolding i_def j_def by auto
    then have i_less_j: "i < j"
      by (metis IntI ST_props(1) equals0D i_le_j order_neq_le_trans)
    then have rm_not_empty: "rm (S \<times> T) \<noteq> {}"
      using S_def T_def i_le_j i_def j_def prod_not_empty ST_props by force
    have rm_finite: "finite (rm (S \<times> T))"
      by (auto simp add: Collect_case_prod_Sigma ST_finite)
    then have set_eq: "set (map (rv_at testi) ps) = rm (S \<times> T)"
      using S_def T_def VStar(3) Star by auto

    from VStar(2) Star have r'_atms: "\<forall>y\<in>regex.atms r'. \<forall>p' \<in> vpatms (VStar ps). test y p' \<longrightarrow> vio (testi p') y"
      by auto

    { fix k
      assume k_in: "k \<in> {0 ..< length ps}"
      then have "Regex_Proof_System.VIO vio (fst (rv_at testi (ps ! k))) (snd (rv_at testi (ps ! k))) r'"
        using VStar(1)[of "ps ! k" r'] Star VStar(2-3) r'_atms by force
    } note k_vio = this

    { fix k
      assume k_in: "k \<in> {0 ..< length ps}"
      then have "rv_at testi (ps ! k) \<in> set (map (rv_at testi) ps)"
        by simp
      then have "(fst (rv_at testi (ps ! k)), snd (rv_at testi (ps ! k))) \<in> rm (S \<times> T)"
        using set_eq by auto
    }
    then have "\<forall>x \<in> set (map (rv_at testi) ps). Regex_Proof_System.VIO vio (fst x) (snd x) r'"
      using k_vio by (force simp: in_set_conv_nth)
    then have st_vio: "\<forall>(s, t) \<in> rm(S \<times> T). Regex_Proof_System.VIO vio s t r'"
      using set_eq[symmetric] by auto
    show ?thesis
      using VStar Star VIO.VStar[OF i_less_j i_in j_in _ _ st_vio] ST_props
        S_def T_def by auto
  qed auto
next
  case (VStar_gt n n')
  then show ?case
    by (auto elim!: rv_check.elims intro: VIO.VStar_gt)
qed

lemma rv_check_complete:
  "(\<forall>x \<in> Regex.atms r. \<forall>i. vio i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')) \<Longrightarrow>
    Regex_Proof_System.VIO vio i j r \<Longrightarrow> i \<le> j \<Longrightarrow> \<exists>p. rv_check test testi r p \<and> rv_at testi p = (i, j)"
proof(induction r arbitrary: i j)
  case (Skip x)
  then have j_noteq: "j \<noteq> i + x"
    using VIO.simps[of vio i j "Regex.Skip x"]
    by simp
  then have "rv_check test testi (Regex.Skip x) (VSkip i j) \<and> rv_at testi (VSkip i j) = (i, j)"
    using Skip(3)
    by auto
  then show ?case
    by (auto intro: exI[of _ "VSkip i j"])
next
  case (Test x)
  then show ?case
  proof (cases "i < j")
    case True
    then show ?thesis
      using rv_check.simps(3)[of test testi x i j] Test
        rv_at.simps(3)[of testi i j]
      by blast
  next
    case False
    then have i_eq_j: "i = j \<and> vio j x"
      using Test VIO.simps[of vio i j "Regex.Test x"]
      by auto
    then obtain p where p_def: "test x p" "testi p = j"
      using Test
      by auto
    then show ?thesis
      using rv_check.simps(2)[of test testi x p] Test
        rv_at.simps(2)[of testi p] i_eq_j
      by blast
  qed
next
  case (Plus r1 r2)
  then have vio_r1: "Regex_Proof_System.VIO vio i j r1" and vio_r2: "Regex_Proof_System.VIO vio i j r2"
    using VIO.simps[of vio i j "Regex.Plus r1 r2"]
    by simp+
  from Plus(3) have r1_atms: "\<forall>x\<in>regex.atms r1. \<forall>i. vio i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')" and
                    r2_atms: "\<forall>x\<in>regex.atms r2. \<forall>i. vio i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')"
    by auto
  from Plus(1)[OF r1_atms vio_r1 Plus(5)] obtain p1 where
    p1_def: "rv_check test testi r1 p1 \<and> rv_at testi p1 = (i, j)"
    by auto
  from Plus(2)[OF r2_atms vio_r2 Plus(5)] obtain p2 where
    p2_def: "rv_check test testi r2 p2 \<and> rv_at testi p2 = (i, j)"
    by auto
  then show ?case
    using rv_check.simps(4)[of test testi r1 r2 p1 p2] p1_def
      rv_at.simps(4)[of testi p1 p2]
    by fastforce
next
  case (Times r1 r2)
  then have k_vio: "\<forall>k \<in> {i .. j}. Regex_Proof_System.VIO vio i k r1 \<or> Regex_Proof_System.VIO vio k j r2"
    using VIO.simps[of vio i j "Regex.Times r1 r2"]
    by simp
  from Times(3) have r1_atms: "\<forall>x\<in>regex.atms r1. \<forall>i. vio i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')" and
                     r2_atms: "\<forall>x\<in>regex.atms r2. \<forall>i. vio i x \<longrightarrow> (\<exists>p'. testi p' = i \<and> test x p')"
    by auto

  {fix k
    assume k_in: "k \<in> {i .. j}"
    then have "(\<exists>p. (rv_check test testi r1 p \<and> rv_at testi p = (i, k)) \<or>
    (rv_check test testi r2 p \<and> rv_at testi p = (k, j)))"
      using k_vio k_in Times by fastforce
  }
  then have k_ex_p: "\<forall>k \<in> {i .. j}. (\<exists>p. (rv_check test testi r1 p \<and> rv_at testi p = (i, k))
    \<or> (rv_check test testi r2 p \<and> rv_at testi p = (k, j)))"
    by auto
  then obtain f where f_def: "\<forall>k \<in> {i .. j}. (rv_check test testi r1 (f k) \<and> rv_at testi (f k) = (i, k))
    \<or> (rv_check test testi r2 (f k) \<and> rv_at testi (f k) = (k, j))"
    using bchoice[OF k_ex_p]
    by atomize_elim auto
  define g where "g = (\<lambda>k. (rv_check test testi r1 (f k) \<and> rv_at testi (f k) = (i, k), f k))"
  then obtain ps where ps_def: "ps = map g [i ..< Suc j]"
    by auto
  then have ps_nnil: "ps \<noteq> []"
    using Times(5) by auto
  then have hd_last_ps: "fst (rv_at testi (snd (hd ps))) = i \<and> snd (rv_at testi (snd (last ps))) = j"
    using g_def f_def ps_def upt_rec[of i j]
    by (auto dest: bspec[of _ _ i] bspec[of _ _ j])
  from ps_def ps_nnil have i_plus_len_eq_j: "i + length ps - 1 = j"
    by auto

  { fix k
    assume k_in: "k \<in> {0 ..< length ps}"
    then obtain k' where k'_def: "k' = i + k \<and> k' \<in> {i .. j}"
      using f_def ps_def ps_nnil Times(5)
      by atomize_elim auto
    then have "if fst (ps ! k) then rv_check test testi r1 (snd (ps ! k)) \<and> rv_at testi (snd (ps ! k)) = (i, i + k)
      else rv_check test testi r2 (snd (ps ! k)) \<and> rv_at testi (snd (ps ! k)) = (i + k, j)"
      using ps_def g_def f_def k_in
      by (auto simp: nth_append dest: bspec[of _ _ j])
  } note k_ps_vio = this

  then show ?case
    using Times rv_check.simps(5)[of test testi r1 r2 ps]
      rv_at.simps(5)[of testi ps] hd_last_ps k_vio i_plus_len_eq_j ps_nnil
    by (auto intro!: exI[of _ "VTimes ps"] simp: split_beta)
next
  case (Star r')
  then obtain S and T where S_def: "i \<in> S" and T_def: "j \<in> T" and
    ST_props: "S \<inter> T = {} \<and> S \<union> T = {i .. j}" and
    st_vio: "\<forall>(s, t)\<in>rm (S \<times> T). Regex_Proof_System.VIO vio s t r'"
    using VIO.simps[of vio i j "Regex.Star r'"]
    by auto
  then have finiteS: "finite S" and finiteT: "finite T"
    using Un_infinite[of S T] infinite_Un[of S T]
    by auto
  from ST_props finiteS finiteT S_def T_def
  have i_min_un: "i = Min (S \<union> T)" and j_max_un:"j = Max (S \<union> T)"
    by (auto simp: Star.prems(3) antisym)
  from i_min_un have i_min: "i = Min S"
    using S_def ST_props finiteS subsetD[of S "S \<union> T"] Min_eqI[of S i]
    by fastforce
  from j_max_un have j_max: "j = Max T"
    using T_def ST_props finiteT subsetD[of T "S \<union> T"] Max_eqI[of T j]
    by fastforce
  from finiteS finiteT have rm_finite: "finite (rm (S \<times> T))"
    by (auto simp add: Collect_case_prod_Sigma)

  then have st_ex_p: "\<forall>k \<in> rm (S \<times> T). \<exists>p. rv_check test testi r' p \<and> rv_at testi p = k"
      using st_vio Star by auto
  then obtain f where f_def: "\<forall>(s,t) \<in> rm (S \<times> T). rv_check test testi r' (f (s,t)) \<and> rv_at testi (f (s,t)) = (s,t)"
    using bchoice[OF st_ex_p]
    by atomize_elim auto
  define ps where "ps = map f (sorted_list_of_set (rm (S \<times> T)))"
  then have ps_nnil: "ps \<noteq> []"
    using ST_props S_def T_def Star(4) sorted_list_of_set[of "rm (S \<times> T)"] rm_finite by fastforce
  from ps_def have ps_check: "\<forall>k \<in> {0 ..< length ps}. rv_check test testi r' (ps ! k)"
    using f_def set_sorted_list_of_set[of "rm (S \<times> T)"] rm_finite
      nth_mem[of _ ps] set_map[of f "sorted_list_of_set (rm (S \<times> T))"] by force

  have map_eq: "map (rv_at testi) ps = sorted_list_of_set (rm (S \<times> T))"
    using set_sorted_list_of_set[OF rm_finite] ps_def f_def
    by (auto intro: map_idI)

  {fix k
    assume k_def: "k \<in> T \<and> (\<forall>j \<in> S. k \<le> j)"
    then have "\<not> (\<exists>k' \<in> rm (S \<times> T). snd k' = k)"
      by auto
    then have "k \<le> i"
      using k_def T_def S_def
      by auto
    then have False
      using k_def ST_props S_def T_def j_max_un antisym
      by fastforce
    then have "\<exists>j \<in> S. j < k"
      by auto
  }note * = this
  then have "\<forall>k \<in> T. \<exists>j \<in> S. j < k"
    using not_le_imp_less
    by blast
  then have "\<forall>k \<in> T. \<exists>k' \<in> rm (S \<times> T). snd k' = k"
    by force
  then have t_snd: "\<forall>k \<in> T. \<exists>k' \<in> set ps. snd (rv_at testi k') = k"
    using ps_def f_def set_sorted_list_of_set[OF rm_finite]
    by fastforce

  {fix k
    assume k_def: "k \<in> S \<and> (\<forall>j \<in> T. k \<ge> j)"
    then have "\<not> (\<exists>k' \<in> rm (S \<times> T). fst k' = k)"
      by auto
    then have "k \<ge> j"
      using k_def T_def
      by auto
    then have False
      using k_def ST_props S_def T_def j_max_un antisym
      by fastforce
    then have "\<exists>j \<in> T. k < j"
      by auto
  }
  then have "\<forall>k \<in> S. \<exists>j \<in> T. k < j"
    using not_le_imp_less
    by blast
  then have "\<forall>k \<in> S. \<exists>k' \<in> rm (S \<times> T). fst k' = k"
    by force
  then have "\<forall>k \<in> S. \<exists>k' \<in> set ps. fst (rv_at testi k') = k"
    using ps_def f_def set_sorted_list_of_set[OF rm_finite]
    by fastforce
  then have st_map: "set (map (fst \<circ> (rv_at testi)) ps) = S \<and> set (map (snd \<circ> (rv_at testi)) ps) = T"
    using ps_def f_def rm_finite sorted_list_of_set[of "rm (S \<times> T)"] t_snd by auto

  then show ?case
    using Star(4) rv_check.simps(6)[of test testi r' ps] rv_at.simps(6)[of testi ps] 
      j_max i_min ps_check st_map map_eq S_def T_def ST_props
    by (auto intro!: exI[of _ "VStar ps"])
qed

lemma rs_check_exec_rs_check:
  fixes test :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and testi :: "'b \<Rightarrow> nat"
  and test' :: " ('n \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  and FV :: "'a \<Rightarrow> 'n set"
  and C :: "'n set \<Rightarrow> ('n \<Rightarrow> 'd) set"
  assumes C_nonemptyI: "\<And>A. C A \<noteq> {}"
  and C_union_eq: "\<And>X Y. C (X \<union> Y) = C X \<inter> C Y"
  and C_Union_eq: "\<And>X (Y :: 'a \<Rightarrow> _). C (\<Union> (Y ` X)) = (\<Inter>x\<in>X. C (Y x))"
  and C_extensible: "\<And>X Y v. v \<in> C X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<exists>v'. v' \<in> C Y \<and> (\<forall>x\<in>X. v x = v' x)"
  and cong: "\<And>v v' x sp. \<forall>a\<in>FV x. v a = v' a \<Longrightarrow> test' v x sp = test' v' x sp"
  shows "(\<And>x sp. x \<in> regex.atms r \<Longrightarrow> test x sp = (\<forall>v\<in>C (FV x). test' v x sp)) \<Longrightarrow>
  rs_check test testi r rsp = (\<forall>v\<in>\<Inter>x\<in>regex.atms r. C (FV x). rs_check (test' v) testi r rsp)"
proof (induct r arbitrary: rsp)
  case (Skip x)
  then show ?case
    by (cases rsp) auto
next
  case (Test x)
  with C_nonemptyI[of "FV x"] show ?case
    by (cases rsp) auto
next
  case (Plus r1 r2)
  with C_nonemptyI[of "Regex.collect FV r1 \<union> Regex.collect FV r2"] show ?case
  proof (cases rsp)
    case (SPlusL sp)
    with Plus show ?thesis
      by (auto 0 4 dest: C_extensible[of _ "Regex.collect FV r1" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          elim!: rs_check_cong[of _ _ _ "test' _" "test' _" testi testi, THEN iffD1, rotated -1, OF _ refl cong refl])
   next
    case (SPlusR sp)
    with Plus show ?thesis
      by (auto 0 4 dest: C_extensible[of _ "Regex.collect FV r2" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          elim!: rs_check_cong[of _ _ _ "test' _" "test' _" testi testi, THEN iffD1, rotated -1, OF _ refl cong refl])
  qed (auto simp: collect_alt INT_Un C_Union_eq C_union_eq)
next
  case (Times r1 r2)
  note * = C_nonemptyI[of "Regex.collect FV r1 \<union> Regex.collect FV r2",
      simplified collect_alt INT_Un C_Union_eq C_union_eq]
  from Times * show ?case
  proof (cases rsp)
    case (STimes sp1 sp2)
    from Times show ?thesis
      unfolding STimes rs_check.simps regex.set INT_Un ball_conj_distrib ball_triv_nonempty[OF *]
      by (auto 0 4
          dest: C_extensible[of _ "Regex.collect FV r1" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          C_extensible[of _ "Regex.collect FV r2" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          elim!: rs_check_cong[of _ _ _ "test' _" "test' _" testi testi, THEN iffD1, rotated -1, OF _ refl cong refl])
  qed auto
next
  case (Star r)
  with C_nonemptyI[of "Regex.collect FV r"] show ?case
    by (cases rsp) (auto simp: collect_alt C_Union_eq)
qed

lemma rv_check_exec_rv_check:
  fixes test :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and testi :: "'b \<Rightarrow> nat"
  and test' :: " ('n \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  and FV :: "'a \<Rightarrow> 'n set"
  and C :: "'n set \<Rightarrow> ('n \<Rightarrow> 'd) set"
  assumes C_nonemptyI: "\<And>A. C A \<noteq> {}"
  and C_union_eq: "\<And>X Y. C (X \<union> Y) = C X \<inter> C Y"
  and C_Union_eq: "\<And>X (Y :: 'a \<Rightarrow> _). C (\<Union> (Y ` X)) = (\<Inter>x\<in>X. C (Y x))"
  and C_extensible: "\<And>X Y v. v \<in> C X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<exists>v'. v' \<in> C Y \<and> (\<forall>x\<in>X. v x = v' x)"
  and cong: "\<And>v v' x sp. \<forall>a\<in>FV x. v a = v' a \<Longrightarrow> test' v x sp = test' v' x sp"
  shows "(\<And>x sp. x \<in> regex.atms r \<Longrightarrow> test x sp = (\<forall>v\<in>C (FV x). test' v x sp)) \<Longrightarrow>
  rv_check test testi r rsp = (\<forall>v\<in>\<Inter>x\<in>regex.atms r. C (FV x). rv_check (test' v) testi r rsp)"
proof (induct r arbitrary: rsp)
  case (Skip x)
  then show ?case
    by (cases rsp) auto
next
  case (Test x)
  with C_nonemptyI[of "FV x"] show ?case
    by (cases rsp) auto
next
  case (Plus r1 r2)
  note * = C_nonemptyI[of "Regex.collect FV r1 \<union> Regex.collect FV r2",
      simplified collect_alt INT_Un C_Union_eq C_union_eq]
  from Plus * show ?case
  proof (cases rsp)
    case (VPlus vp1 vp2)
    from Plus show ?thesis
      unfolding VPlus rv_check.simps regex.set INT_Un ball_conj_distrib ball_triv_nonempty[OF *]
      by (auto 0 4
          dest: C_extensible[of _ "Regex.collect FV r1" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          C_extensible[of _ "Regex.collect FV r2" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          elim!: rv_check_cong[of _ _ _ "test' _" "test' _" testi testi, THEN iffD1, rotated -1, OF _ refl cong refl])
  qed auto
next
  case (Times r1 r2)
  note * = C_nonemptyI[of "Regex.collect FV r1 \<union> Regex.collect FV r2",
      simplified collect_alt INT_Un C_Union_eq C_union_eq]
  from Times * show ?case
  proof (cases rsp)
    case (VTimes ps)
    from Times have IH: "if fst (ps ! k)
      then rv_check test testi r1 (snd (ps ! k)) = (\<forall>v\<in>\<Inter>x\<in>regex.atms r1. C (FV x). rv_check (test' v) testi r1 (snd (ps ! k)))
      else rv_check test testi r2 (snd (ps ! k)) = (\<forall>v\<in>\<Inter>x\<in>regex.atms r2. C (FV x). rv_check (test' v) testi r2 (snd (ps ! k)))"
      if "k < length ps" for k
      using that by auto
    show ?thesis
      unfolding VTimes rv_check.simps regex.set INT_Un ball_conj_distrib ball_triv_nonempty[OF *]
        ex_simps simp_thms ball_swap[of _ "{0 ..< length ps}"] Let_def split_beta ball_if_distrib
      by (intro conj_cong refl ball_cong if_cong)
        (auto 0 4 simp: IH
          dest: C_extensible[of _ "Regex.collect FV r1" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          C_extensible[of _ "Regex.collect FV r2" "Regex.collect FV r1 \<union> Regex.collect FV r2",
            simplified collect_alt C_union_eq C_Union_eq INT_iff]
          elim!: rv_check_cong[of _ _ _ "test' _" "test' _" testi testi, THEN iffD1, rotated -1, OF _ refl cong refl])
  qed auto
next
  case (Star r)
  note * = C_nonemptyI[of "Regex.collect FV r", simplified collect_alt INT_Un C_Union_eq]
  with Star show ?case
  proof (cases rsp)
    case (VStar vps)
    then show ?thesis
      unfolding VStar rv_check.simps regex.set INT_Un ball_conj_distrib ball_triv_nonempty[OF *]
        ex_simps simp_thms ball_swap[of _ "{0 ..< length vps}"]
      by (intro conj_cong refl ball_cong Star) simp
  qed (auto simp: collect_alt C_Union_eq)
qed

lemma chain_sorted1:
  fixes f :: "_ \<Rightarrow> nat \<times> nat"
  assumes "\<forall>k\<in>{Suc 0..<length ps}. fst (f (ps ! k)) = snd (f (ps ! (k - Suc 0)))"
  and "\<forall>k\<in>{0..<length ps}. fst (f (ps ! k)) < snd (f (ps ! k))"
  and "j \<le> k" "k < length ps"
  shows "fst (f (ps ! j)) \<le> fst (f (ps ! k))"
  using assms
proof (induct "k - j" arbitrary: j)
  case (Suc x)
  then show ?case 
    by (cases "k") (force simp: less_Suc_eq dest!: bspec[of _ _ "j"] meta_spec[of _ "Suc j"])+
qed simp

lemma chain_sorted2:
  fixes f :: "_ \<Rightarrow> nat \<times> nat"
  assumes "\<forall>k\<in>{Suc 0..<length ps}. fst (f (ps ! k)) = snd (f (ps ! (k - Suc 0)))"
  and "\<forall>k\<in>{0..<length ps}. fst (f (ps ! k)) < snd (f (ps ! k))"
  and "j \<le> k" "k < length ps"
  shows "snd (f (ps ! j)) \<le> snd (f (ps ! k))"
  using assms
proof (induct "k - j" arbitrary: j)
  case (Suc x)
  then show ?case 
    by (cases "k") (force simp: less_Suc_eq dest!: bspec[of _ _ "Suc j"] meta_spec[of _ "Suc j"])+
qed simp

context
  fixes test :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and testi :: "'b \<Rightarrow> nat" and SAT sat
  assumes test_sound: "\<forall>x\<in>regex.atms r. \<forall>p'\<in>spatms rsp. test x p' \<longrightarrow> SAT (testi p') x"
  and SAT_sound: "\<forall>x\<in>regex.atms r. \<forall>i. SAT i x \<longrightarrow> sat i x"
begin

lemma rs_check_le:
   "rs_check test testi r rsp \<Longrightarrow> fst (rs_at testi rsp) \<le> snd (rs_at testi rsp)"
  by (drule rs_check_sound[OF test_sound], drule soundness_SAT[OF SAT_sound], drule match_le)

lemma rs_check_le1:
  "rs_check test testi r rsp \<Longrightarrow> sp \<in> spatms rsp \<Longrightarrow> fst (rs_at testi rsp) \<le> testi sp"
proof (induct r rsp rule: rs_check.induct)
  case (7 r ps)
  then show ?case
    by (fastforce simp: in_set_conv_nth hd_conv_nth
      intro: order_trans[OF chain_sorted1[of ps "rs_at testi" 0]])
qed (auto dest: rs_check_le)

lemma rs_check_le2:
  "rs_check test testi r rsp \<Longrightarrow> sp \<in> spatms rsp \<Longrightarrow> testi sp \<le> snd (rs_at testi rsp)"
proof (induct r rsp rule: rs_check.induct)
  case (7 r ps)
  then show ?case
    by (fastforce simp: in_set_conv_nth last_conv_nth
      intro: order_trans[OF _ chain_sorted2[of ps "rs_at testi" _ "length ps - Suc 0"]])
qed (auto dest: rs_check_le)

end

lemma rv_check_le:
  "rv_check test testi r rvp \<Longrightarrow> vp \<in> vpatms rvp \<Longrightarrow> fst (rv_at testi rvp) \<le> snd (rv_at testi rvp)"
  by (induct r rvp rule: rv_check.induct) (auto simp: neq_Nil_conv)

lemma rv_check_le2:
  "rv_check test testi r rvp \<Longrightarrow> vp \<in> vpatms rvp \<Longrightarrow> testi vp \<le> snd (rv_at testi rvp)"
proof (induct r rvp rule: rv_check.induct)
  case (5 r r' ps)
  from 5(4) obtain b i rvp where *: "i < length ps" "ps ! i = (b, rvp)" "vp \<in> vpatms rvp"
    unfolding rvproof.set UN_iff Bex_def in_set_conv_nth by auto
  show ?case
  proof (cases b)
    case True
    with * 5(1)[of i "ps ! i" b rvp] 5(3) show ?thesis 
      by (auto dest: bspec[of _ _ i])
  next
    case False
    with * 5(2)[of i "ps ! i" b rvp] 5(3) show ?thesis 
      by (auto dest: bspec[of _ _ i])
  qed
next
  case (6 r ps)
  from 6(3) obtain i rvp where *: "i < length ps" "ps ! i = rvp" "vp \<in> vpatms rvp"
    unfolding rvproof.set UN_iff Bex_def in_set_conv_nth by auto
  with 6(1)[of i] 6(2) show ?case
    by (auto elim!: order_trans)
qed auto

(*<*)
end
(*>*)
