section \<open>A Memoized Implementation of WPO\<close>

theory WPO_Mem_Impl
  imports 
    WPO_Approx
    Indexed_Term
    List_Memo_Functions     
begin

context
  fixes pr :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool)"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and ssimple :: bool
    and large :: "'f \<times> nat \<Rightarrow> bool"
    and cS cNS :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
    and \<sigma> :: "'f status"
    and c :: "'f \<times> nat \<Rightarrow> order_tag"
begin

text \<open>The main implementation working on indexed terms\<close>
fun  
  wpo_mem :: "(('f, 'v) indexed_term) term_rel_mem_type" and
  wpo_main :: "(('f, 'v) indexed_term) term_rel_mem_type"
  where
    "wpo_mem mem (s,t) =
      (let
        i = index s;
        j = index t
      in
        (case Mapping.lookup mem (i,j) of
          Some res \<Rightarrow> (res, mem)
        | None \<Rightarrow> case wpo_main mem (s,t)  
     of (res, mem_new) \<Rightarrow> (res, Mapping.update (i,j) res mem_new)))"
  | "wpo_main mem (s,t) = (let fs = stored s; ft = stored t in 
      if cS fs ft then ((True, True), mem)
      else if cNS fs ft then (
      case s of
      Var x \<Rightarrow> ((False,
        (case t of
          Var y \<Rightarrow> name_of x = name_of y
        | Fun g ts \<Rightarrow> status \<sigma> (name_of g, length ts) = [] \<and> prl (name_of g, length ts))), mem)
    | Fun f ss \<Rightarrow>
        let ff = (name_of f, length ss); sf = status \<sigma> ff; ss' = map (\<lambda> i. ss ! i) sf in
          (case exists_mem (\<lambda> s'. (s',t)) wpo_mem snd mem ss' of
         (wpo_result, mem_out_1) \<Rightarrow>
            if wpo_result then ((True, True), mem_out_1)
            else
              (case t of
                Var _ \<Rightarrow> ((False, ssimple \<and> large ff), mem_out_1)
              | Fun g ts \<Rightarrow>
                let gg = (name_of g, length ts); sg = status \<sigma> gg; ts' = map (\<lambda> i. ts ! i) sg in
                (case pr ff gg of (prs, prns) \<Rightarrow>
                  if prns then 
                  (case forall_mem (\<lambda> t'. (s,t')) wpo_mem fst mem_out_1 ts' of
                    (wpo_result, mem_out_2) \<Rightarrow>
                    if wpo_result then
                      if prs then ((True, True), mem_out_2)
                      else 
                        let cf = c ff; cg = c gg in
                         if cf = Lex \<and> cg = Lex then lex_ext_unbounded_mem wpo_mem mem_out_2 ss' ts'
                         else if cf = Mul \<and> cg = Mul then mul_ext_mem wpo_mem mem_out_2 ss' ts'
                         else if ts' = [] then ((ss' \<noteq> [], True), mem_out_2)
                         else ((False, False), mem_out_2)
                    else ((False, False), mem_out_2)) else ((False,False), mem_out_1))
                  )
            )
        ) else ((False, False), mem))"

declare wpo_mem.simps[simp del]
declare wpo_main.simps[simp del]

text \<open>And the wrapper that computes the indexed terms and initializes the memory.\<close>

definition wpo_mem_impl  :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> (bool \<times> bool)"
  where
    "wpo_mem_impl s t = fst (wpo_mem Mapping.empty (index_term s, index_term t))"

text \<open>Soundness of the implementation\<close>

lemma wpo_mem: fixes rli rri :: "index \<Rightarrow> ('f,'v)term" (* reverse index functions *) 
  assumes 
    wpoub: "wpoub = wpo_ub pr prl ssimple large cS cNS \<sigma> c" 
    and wpo: "wpo = (\<lambda> (s,t). wpoub s t)" 
    and ri: "ri = map_prod rli rri"
    and "\<And> si. fst st \<unrhd> si \<Longrightarrow> rli (index si) = unindex si \<and> stored si = unindex si" 
    and "\<And> ti. snd st \<unrhd> ti \<Longrightarrow> rri (index ti) = unindex ti \<and> stored ti = unindex ti" 
    and "valid_memory wpo ri m" 
  shows "wpo_mem m st = (p,m') \<Longrightarrow> p = wpo (map_prod unindex unindex st) \<and> valid_memory wpo ri m'"
    "wpo_main m st = (p,m') \<Longrightarrow> p = wpo (map_prod unindex unindex st) \<and> valid_memory wpo ri m'"
  using assms(4-)
proof (induct m st and m st arbitrary: p m' and p m' rule: wpo_mem_wpo_main.induct)
  case (1 m s t)
  note IH = 1(1)
  note revi = 1(3,4)[unfolded fst_conv snd_conv]
  note mem = 1(5)
  note res = 1(2)[unfolded wpo wpo_mem.simps Let_def]
  have ri: "ri (index s, index t) = (unindex s, unindex t)" 
    unfolding ri using revi(1)[of s] revi(2)[of t] by auto
  show ?case
  proof (cases "Mapping.lookup m (index s, index t)")
    case (Some q)
    note res = res[unfolded Some option.simps]
    from res have id: "p = q" "m' = m" by auto
    from mem[unfolded valid_memory_def, rule_format, OF Some]
    have "wpo (ri (index s, index t)) = q" by auto
    with ri show ?thesis unfolding id using mem by auto
  next
    case None
    note res = res[unfolded None option.simps]
    obtain res2 mem2 where rec: "wpo_main m (s, t) = (res2, mem2)" by fastforce
    have res2: "res2 = wpo (unindex s, unindex t)" and mem: "valid_memory wpo ri mem2" 
      using IH[OF refl refl None rec revi mem] by auto
    from res[unfolded rec split]
    have p: "p = res2" and m': "m' = Mapping.update (index s, index t) res2 mem2" by auto
    show ?thesis unfolding p res2 m' using mem ri
      by (auto simp add: valid_memory_def lookup_update')
  qed
next
  case (2 m s t)
  let ?s = "unindex s" 
  let ?t = "unindex t" 
  note revi = 2(6,7)[unfolded fst_conv snd_conv]
  from revi(1)[of s] revi(2)[of t]
  have stored: "stored s = unindex s" "stored t = unindex t" by auto
  note IHs = 2(1-4)[OF stored[symmetric]]
  note mem = 2(8)
  note res = 2(5)[unfolded wpo_main.simps Let_def stored]
  have wpo_st: "wpo (unindex s, unindex t) = wpoub (unindex s) (unindex t)" for s t  
    unfolding wpo by simp
  note wpo = this[of s t,unfolded wpoub wpo_ub.simps[of _ _ _ _ _ _ _ _ ?s ?t], folded wpoub]
  show ?case
  proof (cases s)
    case (Var xi)
    then obtain x i where s: "s = Var (x,i)" by (cases xi, auto)
    thus ?thesis using res mem wpo by (cases t, auto)
  next
    case (Fun fi ss)
    then obtain f i where s: "s = Fun (f,i) ss" by (cases fi, auto)
    let ?Sta = "status \<sigma> (f, length ss)" 
    note res = res[unfolded s term.simps name_of.simps, folded s]
    note wpo = wpo[unfolded s unindex.simps term.simps, folded unindex.simps[of _ i], folded s, 
        unfolded length_map Let_def]
    show ?thesis
    proof (rule ccontr)
      assume neg: "\<not> ?thesis" 
      from neg res mem wpo s have ncS: "\<not> cS ?s ?t" by auto
      from neg res mem wpo s ncS have cNS: "cNS ?s ?t" by (auto split: if_splits)
      have id: "map_prod unindex unindex (s,t) = (unindex s, unindex t)" for s t :: "('f,'v)indexed_term" by auto
      define sss where "sss = map ((!) ss) ?Sta" 
      note IHs = IHs[OF ncS cNS s refl refl refl, unfolded name_of.simps, unfolded id fst_conv snd_conv, folded sss_def]
      from ncS cNS have id: "cS ?s ?t = False" "cNS ?s ?t = True" by auto
      note res = res[unfolded id if_True if_False, folded sss_def]
      have sss: "(map ((!) (map unindex ss)) ?Sta) = map unindex sss" 
        unfolding sss_def by (auto dest: set_status_nth[OF refl])
      note wpo = wpo[unfolded id if_True if_False]
      have sss_sub: "set sss \<subseteq> set ss" unfolding sss_def by (auto dest: set_status_nth[OF refl])
      let ?cond1' = "Bex (set sss) (\<lambda>s. snd (wpoub (unindex s) (unindex t)))" 
      let ?cond1'' = "Bex (set ?Sta) (\<lambda>i. snd (wpoub (map unindex ss ! i) (unindex t)))" 
      have "?cond1'' = ?cond1'" unfolding sss_def
        using set_status_nth[OF refl, of _ \<sigma> f ss] by simp
      note wpo = wpo[unfolded this sss]
      let ?cond1 = "exists_mem (\<lambda> s'. (s',t)) wpo_mem snd m sss" 
      obtain b1 m1 where cond1: "?cond1 = (b1,m1)" by fastforce
      {
        fix si
        assume si: "si \<in> set sss" 
        have "wpo_mem m (si, t) = (p, m') \<Longrightarrow>
            valid_memory wpo ri m \<Longrightarrow> p = wpo (unindex si, unindex t) \<and> valid_memory wpo ri m'" 
          for m p m'
          by (intro IHs(1)[OF si _ revi, of m p m'], insert sss_sub s si, auto)
      }
      hence "memoize_fun wpo_mem wpo (map_prod unindex unindex) ri ((\<lambda>s'. (s', t)) ` set sss)" 
        by (intro memoize_funI, auto)
      from exists_mem[OF mem cond1 this]
      have cond1': "?cond1' = b1" and mem1: "valid_memory wpo ri m1" 
        unfolding wpo_st[symmetric] by auto
      note IHs = IHs(2-)[OF cond1[symmetric]]
      note res = res[unfolded cond1 split]
      note wpo = wpo[unfolded cond1']
      from neg res wpo mem1 have b1: "\<not> b1" by auto
      note IHs = IHs[OF this]
      from b1 have b1: "b1 = False" by simp
      note res = res[unfolded b1 if_False]
      note wpo = wpo[unfolded b1 if_False]
      show False
      proof (cases t)
        case (Var yj)
        with neg res wpo mem1 show ?thesis by (cases yj, auto)
      next
        case (Fun gj ts)
        then obtain g j where t: "t = Fun (g,j) ts" by (cases gj, auto)
        let ?f = "(f, length ss)" let ?g = "(g, length ts)"
        obtain prs prns where pr: "pr ?f ?g = (prs, prns)" by force
        let ?sta = "(status \<sigma> (g, length ts))" 
        define tss where "tss = map ((!) ts) ?sta" 
        have tss: "(map ((!) (map unindex ts)) ?sta) = map unindex tss" 
          unfolding tss_def by (auto dest: set_status_nth[OF refl])
        have tss_sub: "set tss \<subseteq> set ts" unfolding tss_def by (auto dest: set_status_nth[OF refl])
        note res = res[unfolded t term.simps name_of.simps pr split, folded tss_def]
        note wpo = wpo[unfolded t unindex.simps term.simps length_map pr split, 
            folded unindex.simps[of _ j], folded t, unfolded tss]
        from neg res mem1 wpo have prns: "prns" by (auto split: if_splits)
        note IHs = IHs[OF t refl refl, unfolded name_of.simps, OF refl pr[symmetric], folded tss_def, OF prns]
        have prns: "(prns \<and> b) = b" "prns = True" for b using prns by auto
        note res = res[unfolded prns if_True]
        note wpo = wpo[unfolded prns(1)]
        let ?cond2 = "forall_mem (\<lambda> t'. (s,t')) wpo_mem fst m1 tss" 
        let ?cond2'' = "Ball (set ?sta) (\<lambda>j. fst (wpoub ?s (map unindex ts ! j)))" 
        let ?cond2' = "Ball (set tss) (\<lambda>t. fst (wpoub ?s (unindex t)))"
        have "?cond2'' = ?cond2'" unfolding tss_def
          using set_status_nth[OF refl, of _ \<sigma> g ts] by simp
        note wpo = wpo[unfolded this]
        obtain b2 m2 where cond2: "?cond2 = (b2,m2)" by force
        {
          fix ti
          assume ti: "ti \<in> set tss" 
          have "wpo_mem m (s, ti) = (p, m') \<Longrightarrow>
            valid_memory wpo ri m \<Longrightarrow> p = wpo (unindex s, unindex ti) \<and> valid_memory wpo ri m'" 
            for m p m'
            by (intro IHs(1)[OF ti _ revi, of m p m'], insert tss_sub t ti, auto)
        }
        hence "memoize_fun wpo_mem wpo (map_prod unindex unindex) ri (Pair s ` set tss)" 
          by (intro memoize_funI, auto)
        from forall_mem[OF mem1 cond2 this]   
        have cond2': "?cond2' = b2" and mem2: "valid_memory wpo ri m2"
          unfolding wpo_st[symmetric] by auto
        note wpo = wpo[unfolded cond2']
        note res = res[unfolded cond2 split]
        from neg res wpo mem2 have b2: b2 by (auto split: if_splits)
        with neg res wpo mem2 have prs: "\<not> prs" by (auto split: if_splits)
        note IHs = IHs(2-)[OF cond2[symmetric] b2 prs refl refl]
        from b2 prs have id: "b2 = True" "prs = False" by auto
        note res = res[unfolded id if_True if_False, folded sss_def tss_def]
        note wpo = wpo[unfolded id if_True if_False]
        let ?is_lex = "c ?f = Lex \<and> c ?g = Lex" 
        show False
        proof (cases ?is_lex)
          case True
          note IH = IHs(1)[OF True]
          from True have lex: "?is_lex = True" by auto
          note res = res[unfolded lex if_True]
          note wpo = wpo[unfolded lex if_True]
          have memo: "memoize_fun wpo_mem wpo (map_prod unindex unindex) ri (set sss \<times> set tss)" 
            apply (rule memoize_fun_pairI)
            apply (rule IH)
                 apply force
                apply force
               apply force
            subgoal by (rule revi, insert sss_sub, auto simp: s)
            subgoal by (rule revi, insert tss_sub, auto simp: t)
            by auto
          have "p = lex_ext_unbounded wpoub (map unindex sss) (map unindex tss) \<and> valid_memory wpo ri m'" 
            by (rule lex_ext_unbounded_mem[OF assms(2) mem2 res memo])
          with res wpo neg
          show ?thesis by auto
        next
          case False
          note IH = IHs(2)[OF False]
          from False have lex: "?is_lex = False" by auto
          note res = res[unfolded lex if_False]
          note wpo = wpo[unfolded lex if_False]
          let ?is_mul = "c (f, length ss) = Mul \<and> c (g, length ts) = Mul" 
          show False
          proof (cases ?is_mul)
            case True
            note IH = IH[OF True]
            from True have mul: "?is_mul = True" by auto
            note res = res[unfolded mul if_True]
            note wpo = wpo[unfolded mul if_True]
            have memo: "memoize_fun wpo_mem wpo (map_prod unindex unindex) ri (set sss \<times> set tss)" 
              apply (rule memoize_fun_pairI)
              apply (rule IH)
                   apply force
                  apply force
                 apply force
              subgoal by (rule revi, insert sss_sub, auto simp: s)
              subgoal by (rule revi, insert tss_sub, auto simp: t)
              by auto
            have "p = mul_ext_impl wpoub (map unindex sss) (map unindex tss) \<and> valid_memory wpo ri m'" 
              using mul_ext_mem(1)[OF assms(2) mem2 res memo] by auto
            with res wpo neg 
            show ?thesis unfolding mul_ext_code by auto
          next
            case False
            from False have mul: "?is_mul = False" by auto
            note res = res[unfolded mul if_False]
            note wpo = wpo[unfolded mul if_False]
            from res wpo neg mem2 show False by (auto split: if_splits)
          qed
        qed
      qed
    qed
  qed
qed

declare [[code drop: wpo_ub]]

lemma wpo_ub_memoized_code[code]: 
  "wpo_ub pr prl ssimple large cS cNS \<sigma> c s t = wpo_mem_impl s t"
proof -
  let ?s = "index_term s" 
  let ?t = "index_term t" 
  let ?m = "Mapping.empty :: term_rel_mem" 
  have m: "valid_memory (\<lambda>(s, t). wpo_ub pr prl ssimple large cS cNS \<sigma> c s t) (map_prod rl rr) ?m" for rl rr
    unfolding valid_memory_def by auto
  from index_term_index_unindex[of s] obtain f where f: "\<forall>t\<unlhd> index_term s. f (index t) = unindex t \<and> stored t = unindex t" by auto
  from index_term_index_unindex[of t] obtain g where g: "\<forall>s\<unlhd> index_term t. g (index s) = unindex s \<and> stored s = unindex s" by auto
  obtain p m where res: "wpo_mem ?m (?s,?t) = (p,m)" by fastforce
  hence impl: "wpo_mem_impl s t = p" unfolding wpo_mem_impl_def by simp
  also have "...   = wpo_ub pr prl ssimple large cS cNS \<sigma> c (unindex (index_term s)) (unindex (index_term t))" 
    by (rule wpo_mem(1)[THEN conjunct1, OF refl refl refl _ _ m res, unfolded map_prod_simp split fst_conv snd_conv, of f g])
      (insert f g, auto)
  finally show ?thesis by simp
qed
end
end
