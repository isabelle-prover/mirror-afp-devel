section \<open>An Approximation of WPO\<close>

text \<open>We define an approximation of WPO. 

  It replaces the bounded lexicographic comparison by an unbounded one.
  Hence, no runtime check on lenghts are required anymore, but instead the arities of the inputs
  have to be bounded via an assumption.

  Moreover, instead of checking that terms are strictly or non-strictly decreasing w.r.t. the
  algebra (i.e., the input reduction pair), we just demand that there are sufficient criteria to
  ensure a strict- or non-strict decrease.\<close>

theory WPO_Approx
imports
  Weighted_Path_Order.WPO
begin

definition compare_bools :: "bool \<times> bool \<Rightarrow> bool \<times> bool \<Rightarrow> bool"
  where
    "compare_bools p1 p2 \<longleftrightarrow> (fst p1 \<longrightarrow> fst p2) \<and> (snd p1 \<longrightarrow> snd p2)"

notation compare_bools ("(_/ \<le>\<^sub>c\<^sub>b _)" [51, 51] 50)

lemma lex_ext_unbounded_cb:
  assumes "\<And> i. i < length xs \<Longrightarrow> i < length ys \<Longrightarrow> f (xs ! i) (ys ! i) \<le>\<^sub>c\<^sub>b g (xs ! i) (ys ! i)"
  shows "lex_ext_unbounded f xs ys \<le>\<^sub>c\<^sub>b lex_ext_unbounded g xs ys"
  unfolding compare_bools_def
  by (rule lex_ext_unbounded_mono,
  insert assms[unfolded compare_bools_def], auto)

lemma mul_ext_cb:
  assumes "\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<le>\<^sub>c\<^sub>b g x y"
  shows "mul_ext f xs ys \<le>\<^sub>c\<^sub>b mul_ext g xs ys"
  unfolding compare_bools_def
  by (intro conjI impI; rule mul_ext_mono) (insert assms, auto simp: compare_bools_def)

context
  fixes pr :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool)"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and ssimple :: bool
    and large :: "'f \<times> nat \<Rightarrow> bool"
    and cS cNS :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" \<comment> \<open>sufficient criteria\<close>
    and \<sigma> :: "'f status"
    and c :: "'f \<times> nat \<Rightarrow> order_tag"
begin

fun wpo_ub  :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" 
  where
    "wpo_ub s t = (if cS s t then (True, True) else if cNS s t then (case s of
      Var x \<Rightarrow> (False,
        (case t of
          Var y \<Rightarrow> x = y
        | Fun g ts \<Rightarrow> status \<sigma> (g, length ts) = [] \<and> prl (g, length ts)))
    | Fun f ss \<Rightarrow>
        let ff = (f, length ss); sf = status \<sigma> ff in
          if (\<exists> i \<in> set sf. snd (wpo_ub (ss ! i) t)) then (True, True)
          else
            (case t of
              Var _ \<Rightarrow> (False, ssimple \<and> large ff)
            | Fun g ts \<Rightarrow>
              let gg = (g, length ts); sg = status \<sigma> gg in
              (case pr ff gg of (prs, prns) \<Rightarrow>
                if prns \<and> (\<forall> j \<in> set sg. fst (wpo_ub s (ts ! j))) then
                  if prs then (True, True)
                  else 
                    let ss' = map (\<lambda> i. ss ! i) sf;
                        ts' = map (\<lambda> i. ts ! i) sg;
                        cf = c ff;
                        cg = c gg in
                     if cf = Lex \<and> cg = Lex then lex_ext_unbounded wpo_ub ss' ts'
                     else if cf = Mul \<and> cg = Mul then mul_ext wpo_ub ss' ts'
                     else if ts' = [] then (ss' \<noteq> [], True) else (False, False)
                else (False, False)))
        ) else (False, False))"

declare wpo_ub.simps [simp del]

abbreviation "wpo_orig n S NS \<equiv> wpo.wpo n S NS pr prl \<sigma> c ssimple large" 

text \<open>soundness of approximation: @{const wpo_ub} can be simulated by @{const wpo_orig}
  if the arities are small (usually the length of the status of f is smaller than the arity of f).\<close>

lemma wpo_ub:
  assumes "\<And> si tj. s \<unrhd> si \<Longrightarrow> t \<unrhd> tj \<Longrightarrow> (cS si tj, cNS si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)"
    and "\<And> f. f \<in> funas_term t \<Longrightarrow> length (status \<sigma> f) \<le> n"
  shows "wpo_ub s t \<le>\<^sub>c\<^sub>b wpo_orig n S NS s t" 
  using assms
proof (induct s t rule: wpo.wpo.induct [of S NS \<sigma> _ n pr prl c ssimple large])
  case (1 s t) 
  note IH = 1(1-4)
  note cb = 1(5)
  note n = 1(6)
  note cbd = compare_bools_def
  note simps = wpo_ub.simps[of s t] wpo.wpo.simps[of n S NS pr prl \<sigma> c ssimple large s t]
  let ?wpo = "wpo_orig n S NS"
  let ?cb = "\<lambda> s t. (cS s t, cNS s t) \<le>\<^sub>c\<^sub>b ((s, t) \<in> S, (s, t) \<in> NS)"
  let ?goal = "\<lambda> s t. wpo_ub s t \<le>\<^sub>c\<^sub>b ?wpo s t"
  from cb[of s t] have cb_st: "?cb s t" by auto
  show ?case
  proof (cases "(s,t) \<in> S \<or> \<not> cNS s t")
    case True
    with cb_st show ?thesis unfolding simps unfolding cbd by auto
  next
    case False
    with cb_st have *: "(s,t) \<notin> S" "(s,t) \<in> NS" "((s,t) \<notin> S) = True" "((s, t) \<in> S) = False" 
      "((s,t) \<in> NS) = True" "cS s t = False" "cNS s t = True"
      unfolding cbd by auto
    note simps = simps[unfolded * if_False if_True]
    note IH = IH[OF *(1-2)]
    show ?thesis
    proof (cases s)
      case (Var x) note s = this
      show ?thesis
      proof (cases t)
        case (Var y) note t = this
        show ?thesis unfolding simps unfolding s t cbd by simp
      next
        case (Fun g ts) note t = this
        show ?thesis unfolding simps unfolding s t cbd by auto
      qed
    next
      case s: (Fun f ss)
      let ?f = "(f,length ss)"
      let ?sf = "status \<sigma> ?f"
      let ?s = "Fun f ss"
      note IH = IH[OF s]
      show ?thesis
      proof (cases "(\<exists> i \<in> set ?sf. snd (?wpo (ss ! i) t))")
        case True
        then show ?thesis unfolding simps using True * unfolding s cbd by auto
      next
        case False
        {
          fix i
          assume i: "i \<in> set ?sf"
          from status_aux[OF i] 
          have "?goal (ss ! i) t"
            by (intro IH(1)[OF i cb n], auto simp: s)
        }
        with False have sub: "(\<exists> i \<in> set ?sf. snd (wpo_ub (ss ! i) t)) = False" unfolding cbd by auto
        note IH = IH(2-4)[OF False]
        show ?thesis
        proof (cases "wpo_ub s t = (False,False)")
          case True
          then show ?thesis unfolding cbd by auto
        next
          case False note noFF = this
          note False = False[unfolded simps * Let_def, unfolded s term.simps sub, simplified]
          show ?thesis
          proof (cases t)
            case t: (Var y)
            from False[unfolded t, simplified]
            show ?thesis unfolding s t unfolding cbd
              using * s simps sub t by auto
          next
            case t: (Fun g ts)
            let ?g = "(g,length ts)"
            let ?sg = "status \<sigma> ?g"
            let ?t = "Fun g ts"
            obtain ps pns where p: "pr ?f ?g = (ps, pns)" by force
            note IH = IH[OF t p[symmetric]]
            note False = False[unfolded t p split term.simps]
            from False have pns: "pns = True" by (cases pns, auto)
            {
              fix j
              assume j: "j \<in> set ?sg"
              from status_aux[OF j] 
              have cb: "?goal s (ts ! j)"
                by (intro IH(1)[OF j cb n], auto simp: t)
              from j False have "fst (wpo_ub s (ts ! j))" unfolding s by (auto split: if_splits)
              with cb have "fst (?wpo s (ts ! j))" unfolding cbd by auto
            }
            then have cond: "pns \<and> (\<forall> j \<in> set ?sg. fst (?wpo s (ts ! j)))" using pns by auto
            note IH = IH(2-3)[OF cond]
            from cond have cond: "(pns \<and> (\<forall> j \<in> set ?sg. fst (?wpo ?s (ts ! j)))) = True" unfolding s by simp
            note simps = simps[unfolded * Let_def, unfolded s t term.simps if_False if_True sub[unfolded t] p split cond]
            show ?thesis 
            proof (cases ps)
              case True
              then show ?thesis unfolding s t unfolding simps cbd by auto
            next
              case False
              note IH = IH[OF this refl refl refl refl]
              let ?msf = "map ((!) ss) ?sf"
              let ?msg = "map ((!) ts) ?sg"
              have set_msf: "set ?msf \<subseteq> set ss" using status[of \<sigma> f "length ss"]
                unfolding set_conv_nth by force
              have set_msg: "set ?msg \<subseteq> set ts" using status[of \<sigma> g "length ts"]
                unfolding set_conv_nth by force
              {
                fix i
                assume "i < length ?msf"
                then have "?msf ! i \<in> set ?msf" unfolding set_conv_nth by blast
                with set_msf have "?msf ! i \<in> set ss" by auto
              } note msf = this
              {
                fix i
                assume "i < length ?msg"
                then have "?msg ! i \<in> set ?msg" unfolding set_conv_nth by blast
                with set_msg have "?msg ! i \<in> set ts" by auto
              } note msg = this
              show ?thesis
              proof (cases "c ?f = Lex \<and> c ?g = Lex")
                case Lex: True
                note IH = IH(1)[OF Lex _ _ cb n, unfolded s t length_map]
                from n[of ?g, unfolded t] have "length (?msg) \<le> n" by auto
                then have ub: "lex_ext_unbounded ?wpo ?msf ?msg =
                  lex_ext ?wpo n ?msf ?msg" 
                  unfolding lex_ext_unbounded_iff lex_ext_iff by auto
                from Lex False simps noFF  
                have wpo_ub: "wpo_ub s t = lex_ext_unbounded wpo_ub ?msf ?msg"
                  unfolding s t using False by (auto split: if_splits)
                also have "\<dots> \<le>\<^sub>c\<^sub>b lex_ext_unbounded ?wpo ?msf ?msg"
                  by (rule lex_ext_unbounded_cb, rule IH) (insert msf msg, auto)
                finally show ?thesis unfolding ub s t simps(2) cbd using Lex by auto
              next
                case nLex: False
                show ?thesis
                proof (cases "c ?f = Mul \<and> c ?g = Mul")
                  case Mul: True
                  note IH = IH(2)[OF nLex Mul _ _ cb n, unfolded s t]
                  from Mul nLex False simps noFF  
                  have wpo_ub: "wpo_ub s t = mul_ext wpo_ub ?msf ?msg"
                    unfolding s t using False by (auto split: if_splits)
                  also have "\<dots> \<le>\<^sub>c\<^sub>b mul_ext ?wpo ?msf ?msg"
                    by (rule mul_ext_cb, rule IH) (insert set_msf set_msg, auto)
                  finally show ?thesis unfolding s t simps(2) cbd using nLex Mul by auto
                next
                  case nMul: False
                  thus ?thesis unfolding s t simps cbd using nLex nMul noFF False
                    by auto
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
end
