section \<open>A List-Based Implementation to Decide Pattern Completeness\<close>

theory Pattern_Completeness_List
  imports 
    Pattern_Completeness_Multiset
    Compute_Nonempty_Infinite_Sorts
    "HOL-Library.AList" 
begin

subsection \<open>Definition of Algorithm\<close>

text \<open>We refine the non-deterministic multiset based implementation
  to a deterministic one which uses lists as underlying data-structure.
  For matching problems we distinguish several different shapes.\<close>

type_synonym ('a,'b)alist = "('a \<times> 'b)list"
type_synonym ('f,'v,'s)match_problem_list = "(('f,nat \<times> 's)term \<times> ('f,'v)term) list" \<comment> \<open>mp with arbitrary pairs\<close>
type_synonym ('f,'v,'s)match_problem_lx = "((nat \<times> 's) \<times> ('f,'v)term) list"  \<comment> \<open>mp where left components are variable\<close>
type_synonym ('f,'v,'s)match_problem_rx = "('v,('f,nat \<times> 's)term list) alist \<times> bool" \<comment> \<open>mp where right components are variables\<close>
type_synonym ('f,'v,'s)match_problem_lr = "('f,'v,'s)match_problem_lx \<times> ('f,'v,'s)match_problem_rx" \<comment> \<open>a partitioned mp\<close>
type_synonym ('f,'v,'s)pat_problem_list = "('f,'v,'s)match_problem_list list" 
type_synonym ('f,'v,'s)pat_problem_lr = "('f,'v,'s)match_problem_lr list" 
type_synonym ('f,'v,'s)pats_problem_list = "('f,'v,'s)pat_problem_list list" 
type_synonym ('f,'v,'s)pat_problem_set_impl = "(('f,nat \<times> 's)term \<times> ('f,'v)term) list list" 

abbreviation mp_list :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_mset" 
  where "mp_list \<equiv> mset" 

abbreviation mp_lx :: "('f,'v,'s)match_problem_lx \<Rightarrow> ('f,'v,'s)match_problem_list" 
  where "mp_lx \<equiv> map (map_prod Var id)" 

definition mp_rx :: "('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_mset"
  where "mp_rx mp = mset (List.maps (\<lambda> (x,ts). map (\<lambda> t. (t,Var x)) ts) (fst mp))" 

definition mp_rx_list :: "('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_list"
  where "mp_rx_list mp = List.maps (\<lambda> (x,ts). map (\<lambda> t. (t,Var x)) ts) (fst mp)" 

definition mp_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> ('f,'v,'s)match_problem_mset"
  where "mp_lr pair = (case pair of (lx,rx) \<Rightarrow> mp_list (mp_lx lx) + mp_rx rx)" 

definition mp_lr_list :: "('f,'v,'s)match_problem_lr \<Rightarrow> ('f,'v,'s)match_problem_list"
  where "mp_lr_list pair = (case pair of (lx,rx) \<Rightarrow> mp_lx lx @ mp_rx_list rx)" 

definition pat_lr :: "('f,'v,'s)pat_problem_lr \<Rightarrow> ('f,'v,'s)pat_problem_mset"
  where "pat_lr ps = mset (map mp_lr ps)" 

definition pat_mset_list :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_mset"
  where "pat_mset_list ps = mset (map mp_list ps)" 

definition pat_list :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_set"
  where "pat_list ps = set ` set ps" 

abbreviation pats_mset_list :: "('f,'v,'s)pats_problem_list \<Rightarrow> ('f,'v,'s)pats_problem_mset" 
  where "pats_mset_list \<equiv> mset o map pat_mset_list" 
 
definition subst_match_problem_list :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_list" where
  "subst_match_problem_list \<tau> = map (subst_left \<tau>)" 

definition subst_pat_problem_list :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_list" where
  "subst_pat_problem_list \<tau> = map (subst_match_problem_list \<tau>)" 

definition match_var_impl :: "('f,'v,'s)match_problem_lr \<Rightarrow> ('f,'v,'s)match_problem_lr" where
  "match_var_impl mp = (case mp of (xl,(rx,b)) \<Rightarrow>
     let xs = remdups (List.maps (vars_term_list o snd) xl)
     in (xl,(filter (\<lambda> (x,ts). tl ts \<noteq> [] \<or> x \<in> set xs) rx),b))" 

definition find_var :: "('f,'v,'s)match_problem_lr list \<Rightarrow> _" where "find_var p = (case concat (map (\<lambda> (lx,_). lx) p) of
      (x,t) # _ \<Rightarrow> x
    | [] \<Rightarrow> let (_,rx,b) = hd (filter (Not o snd o snd) p)
         in case hd rx of (x, s # t # _) \<Rightarrow> hd (the (conflicts s t)))" 

definition empty_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool" where
  "empty_lr mp = (case mp of (lx,rx,_) \<Rightarrow> lx = [] \<and> rx  = [])" 

context pattern_completeness_context
begin


text \<open>insert an element into the part of the mp that stores pairs of form (t,x) for variables x.
   Internally this is represented as maps (assoc lists) from x to terms t1,t2,... so that linear terms are easily
   identifiable. Duplicates will be removed and clashes will be immediately be detected and result in None.\<close>
definition insert_rx :: "('f,nat \<times> 's)term \<Rightarrow> 'v \<Rightarrow> ('f,'v,'s)match_problem_rx \<Rightarrow> ('f,'v,'s)match_problem_rx option" where
  "insert_rx t x rxb = (case rxb of (rx,b) \<Rightarrow> (case map_of rx x of 
    None \<Rightarrow> Some (((x,[t]) # rx, b))
  | Some ts \<Rightarrow> (case those (map (conflicts t) ts)
       of None \<Rightarrow> None \<comment> \<open>clash\<close>
        | Some cs \<Rightarrow> if [] \<in> set cs then Some rxb \<comment> \<open>empty conflict means (t,x) was already part of rxb\<close>
          else Some ((AList.update x (t # ts) rx, b \<or> (\<exists> y \<in> set (concat cs). inf_sort (snd y))))
       )))"

lemma size_zip[termination_simp]: "length ts = length ls \<Longrightarrow> size_list (\<lambda>p. size (snd p)) (zip ts ls) 
  < Suc (size_list size ls)"  
  by (induct ts ls rule: list_induct2, auto)

text \<open>Decomposition applies decomposition, duplicate and clash rule to classify all remaining problems 
  as being of kind (x,f(l1,..,ln)) or (t,x).\<close>
fun decomp_impl :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_lr option" where
  "decomp_impl [] = Some ([],([],False))"
| "decomp_impl ((Fun f ts, Fun g ls) # mp) = (if (f,length ts) = (g,length ls) then 
     decomp_impl (zip ts ls @ mp) else None)" 
| "decomp_impl ((Var x, Fun g ls) # mp) = (case decomp_impl mp of Some (lx,rx) \<Rightarrow> Some ((x,Fun g ls) # lx,rx) 
       | None \<Rightarrow> None)" 
| "decomp_impl ((t, Var y) # mp) = (case decomp_impl mp of Some (lx,rx) \<Rightarrow> 
       (case insert_rx t y rx of Some rx' \<Rightarrow> Some (lx,rx') | None \<Rightarrow> None)
       | None \<Rightarrow> None)" 

definition match_steps_impl :: "('f,'v,'s)match_problem_list \<Rightarrow> ('f,'v,'s)match_problem_lr option" where
  "match_steps_impl mp = map_option match_var_impl (decomp_impl mp)" 

fun pat_inner_impl :: "('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_lr \<Rightarrow> ('f,'v,'s)pat_problem_lr option" where
  "pat_inner_impl [] pd = Some pd" 
| "pat_inner_impl (mp # p) pd = (case match_steps_impl mp of 
     None \<Rightarrow> pat_inner_impl p pd
   | Some mp' \<Rightarrow> if empty_lr mp' then None
       else pat_inner_impl p (mp' # pd))" 

definition pat_impl :: "nat \<Rightarrow> ('f,'v,'s)pat_problem_list \<Rightarrow> ('f,'v,'s)pat_problem_list list option" where
  "pat_impl n p = (case pat_inner_impl p [] of None \<Rightarrow> Some []
      | Some p' \<Rightarrow> (if (\<forall> mp \<in> set p'. snd (snd mp)) then None \<comment> \<open>detected inf-var-conflict (or empty mp)\<close>
        else let p'l = map mp_lr_list p';
           x = find_var p'
         in
           Some (map (\<lambda> \<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x))))" 

partial_function (tailrec) pats_impl :: "nat \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pats_impl n ps = (case ps of [] \<Rightarrow> True
     | p # ps1 \<Rightarrow> (case pat_impl n p of 
         None \<Rightarrow> False
       | Some ps2 \<Rightarrow> pats_impl (n + m) (ps2 @ ps1)))"

definition pat_complete_impl :: "('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "pat_complete_impl ps = (let 
      n = Suc (max_list (List.maps (map fst o vars_term_list o fst) (concat (concat ps))))
     in pats_impl n ps)" 
end

lemmas pat_complete_impl_code = 
  pattern_completeness_context.pat_complete_impl_def
  pattern_completeness_context.pats_impl.simps
  pattern_completeness_context.pat_impl_def
  pattern_completeness_context.\<tau>s_list_def
  pattern_completeness_context.insert_rx_def
  pattern_completeness_context.decomp_impl.simps
  pattern_completeness_context.match_steps_impl_def
  pattern_completeness_context.pat_inner_impl.simps

declare pat_complete_impl_code[code]


subsection \<open>Partial Correctness of the Implementation\<close>

text \<open>We prove that the list-based implementation is 
  a refinement of the multiset-based one.\<close>

lemma mset_concat_union:
  "mset (concat xs) = \<Sum>\<^sub># (mset (map mset xs))"
  by (induct xs, auto simp: union_commute)

lemma in_map_mset[intro]:
  "a \<in># A \<Longrightarrow> f a \<in># image_mset f A"
  unfolding in_image_mset by simp


lemma mset_update: "map_of xs x = Some y \<Longrightarrow>
  mset (AList.update x z xs) = (mset xs - {# (x,y) #}) + {# (x,z) #}" 
  by (induction xs, auto)

lemma set_update: "map_of xs x = Some y \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> 
  set (AList.update x z xs) = insert (x,z) (set xs - {(x,y)})" 
  by (induction xs, auto)

context pattern_completeness_context_with_assms  
begin

text \<open>Various well-formed predicates for intermediate results\<close>

definition wf_ts :: "('f, nat \<times> 's) term list \<Rightarrow> bool"  where 
  "wf_ts ts = (ts \<noteq> [] \<and> distinct ts \<and> (\<forall> j < length ts. \<forall> i < j. conflicts (ts ! i) (ts ! j) \<noteq> None))" 

definition wf_ts2 :: "('f, nat \<times> 's) term list \<Rightarrow> bool"  where 
  "wf_ts2 ts = (length ts \<ge> 2 \<and> distinct ts \<and> (\<forall> j < length ts. \<forall> i < j. conflicts (ts ! i) (ts ! j) \<noteq> None))" 

definition wf_lx :: "('f,'v,'s)match_problem_lx \<Rightarrow> bool" where
  "wf_lx lx = (Ball (snd ` set lx) is_Fun)" 

definition wf_rx :: "('f,'v,'s)match_problem_rx \<Rightarrow> bool" where
  "wf_rx rx = (distinct (map fst (fst rx)) \<and> (Ball (snd ` set (fst rx)) wf_ts) \<and> snd rx = inf_var_conflict (set_mset (mp_rx rx)))" 

definition wf_rx2 :: "('f,'v,'s)match_problem_rx \<Rightarrow> bool" where
  "wf_rx2 rx = (distinct (map fst (fst rx)) \<and> (Ball (snd ` set (fst rx)) wf_ts2) \<and> snd rx = inf_var_conflict (set_mset (mp_rx rx)))" 

definition wf_lr :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "wf_lr pair = (case pair of (lx,rx) \<Rightarrow> wf_lx lx \<and> wf_rx rx)" 

definition wf_lr2 :: "('f,'v,'s)match_problem_lr \<Rightarrow> bool"
  where "wf_lr2 pair = (case pair of (lx,rx) \<Rightarrow> wf_lx lx \<and> (if lx = [] then wf_rx2 rx else wf_rx rx))" 

definition wf_pat_lr :: "('f,'v,'s)pat_problem_lr \<Rightarrow> bool" where
  "wf_pat_lr mps = (Ball (set mps) (\<lambda> mp. wf_lr2 mp \<and> \<not> empty_lr mp))" 

lemma mp_step_mset_cong: 
  assumes "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* mp mp'"
  shows "(add_mset (add_mset mp p) P, add_mset (add_mset mp' p) P) \<in> \<Rrightarrow>\<^sup>*" 
  using assms
proof induct
  case (step mp' mp'')
  from P_simp_pp[OF pat_simp_mp[OF step(2), of p], of P]
  have "(add_mset (add_mset mp' p) P, add_mset (add_mset mp'' p) P) \<in> P_step" 
    unfolding P_step_def by auto
  with step(3)
  show ?case by simp
qed auto

lemma mp_step_mset_vars: assumes "mp \<rightarrow>\<^sub>m mp'"
  shows "tvars_mp (mp_mset mp) \<supseteq> tvars_mp (mp_mset mp')" 
  using assms by induct (auto simp: tvars_mp_def set_zip)

lemma mp_step_mset_steps_vars: assumes "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* mp mp'"
  shows "tvars_mp (mp_mset mp) \<supseteq> tvars_mp (mp_mset mp')" 
  using assms by (induct, insert mp_step_mset_vars, auto)

text \<open>Continue with properties of the sub-algorithms\<close>

lemma insert_rx: assumes res: "insert_rx t x rxb = res"
  and wf: "wf_rx rxb" 
  and mp: "mp = (ls,rxb)" 
  shows "res = Some rx' \<Longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (add_mset (t,Var x) (mp_lr mp + M)) (mp_lr (ls,rx') + M) \<and> wf_rx rx'"
    "res = None \<Longrightarrow> match_fail (add_mset (t,Var x) (mp_lr mp + M))"     
proof -
  obtain rx b where rxb: "rxb = (rx,b)" by force
  note [simp] = List.maps_def
  note res = res[unfolded insert_rx_def]
  {
    assume *: "res = None" 
    with res rxb obtain ts where look: "map_of rx x = Some ts" by (auto split: option.splits)
    with res[unfolded look Let_def rxb split] * obtain t' where t': "t' \<in> set ts" and clash: "Conflict_Clash t t'" 
      by (auto split: if_splits option.splits)
    from map_of_SomeD[OF look] t' have "(t',Var x) \<in># mp_rx rxb"
        unfolding mp_rx_def rxb by auto
    hence "(t',Var x) \<in># mp_lr mp + M" unfolding mp mp_lr_def by auto
    then obtain mp' where mp: "mp_lr mp + M = add_mset (t',Var x) mp'" by (rule mset_add)    
    show "match_fail (add_mset (t,Var x) (mp_lr mp + M))" unfolding mp  
      by (rule match_clash'[OF clash])
  }
  {
    assume "res = Some rx'" 
    note res = res[unfolded this rxb split]
    show "mp_step_mset^** (add_mset (t,Var x) (mp_lr mp + M)) (mp_lr (ls,rx') + M) \<and> wf_rx rx'"
    proof (cases "map_of rx x")
      case look: None
      from res[unfolded this] 
      have rx': "rx' = ((x,[t]) # rx, b)" by auto
      have id: "mp_rx rx' = add_mset (t, Var x) (mp_rx rxb)"
        using look unfolding mp_rx_def mset_concat_union mset_map rx' o_def rxb
        by auto
      have [simp]: "(x, t) \<notin> set rx" for t using look 
        using weak_map_of_SomeI by force
      have "inf_var_conflict (mp_mset (mp_rx ((x, [t]) # rx, b))) = inf_var_conflict (mp_mset (mp_rx (rx, b)))" 
        unfolding mp_rx_def fst_conv inf_var_conflict_def
        by (intro ex_cong1, auto)
      hence wf: "wf_rx rx'" using wf look unfolding wf_rx_def rx' rxb by (auto simp: wf_ts_def)
      show ?thesis unfolding mp mp_lr_def split id
        using wf unfolding rx' by auto
    next
      case look: (Some ts)
      from map_of_SomeD[OF look] have mem: "(x,ts) \<in> set rx" by auto
      note res = res[unfolded look option.simps Let_def]
      from res obtain cs where those: "those (map (conflicts t) ts) = Some cs" by (auto split: option.splits)
      note res = res[unfolded those option.simps]
      from arg_cong[OF those[unfolded those_eq_Some], of set] have confl: "conflicts t ` set ts = Some ` set cs" by auto
      show ?thesis
      proof (cases "[] \<in> set cs")
        case True
        with res have rx': "rx' = rxb" by (auto split: if_splits simp: mp rxb those)
        from True confl obtain t' where "t' \<in> set ts" and "conflicts t t' = Some []" by force
        hence t: "t \<in> set ts" using conflicts(5)[of t t'] by auto  
        hence "(t, Var x) \<in># mp_rx rxb" unfolding mp_rx_def rxb using mem by auto
        hence "(t, Var x) \<in># mp_lr mp + M" unfolding mp mp_lr_def by auto
        then obtain sub where id: "mp_lr mp + M = add_mset (t, Var x) sub" by (rule mset_add)
        show ?thesis unfolding id rx' mp[symmetric] using match_duplicate[of "(t, Var x)" sub] wf by auto
      next
        case False
        with res have rx': "rx' = (AList.update x (t # ts) rx, b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y)))" by (auto split: if_splits)
        from split_list[OF mem] obtain rx1 rx2 where rx: "rx = rx1 @ (x,ts) # rx2" by auto 
        have id: "mp_rx rx' = add_mset (t, Var x) (mp_rx rxb)" 
          unfolding rx' mp_rx_def rxb by (simp add: mset_update[OF look] mset_concat_union, auto simp: rx)
        from wf[unfolded wf_rx_def] rx rxb have ts: "wf_ts ts" and b: "b = inf_var_conflict (mp_mset (mp_rx rxb))" by auto
        from False confl conflicts(5)[of t t] have t: "t \<notin> set ts" by force
        from confl have "None \<notin> set (map (conflicts t) ts)" by auto
        with ts t have ts': "wf_ts (t # ts)" unfolding wf_ts_def 
          apply clarsimp
          subgoal for j i by (cases j, force, cases i; force simp: set_conv_nth)
          done
        have b: "(b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y))) = inf_var_conflict (mp_mset (add_mset (t, Var x) (mp_rx rxb)))" (is "_ = ?ivc")
        proof (standard, elim disjE bexE)
          show "b \<Longrightarrow> ?ivc" unfolding b inf_var_conflict_def by force
          {
            fix y
            assume y: "y \<in> set (concat cs)" and inf: "inf_sort (snd y)" 
            from y confl obtain t' ys where t': "t' \<in> set ts" and c: "conflicts t t' = Some ys" and y: "y \<in> set ys" unfolding set_concat
              by (smt (verit, del_insts) UnionE image_iff)
            have y: "Conflict_Var t t' y" using c y by auto
            from mem t' have "(t',Var x) \<in># mp_rx rxb" unfolding rxb mp_rx_def by auto  
            thus ?ivc unfolding inf_var_conflict_def using inf y by fastforce
          }
          assume ?ivc
          from this[unfolded inf_var_conflict_def]
          obtain s1 s2 x' y
            where ic: "(s1, Var x') \<in># add_mset (t, Var x) (mp_rx rxb) \<and> (s2, Var x') \<in># add_mset (t, Var x) (mp_rx rxb) \<and> Conflict_Var s1 s2 y \<and> inf_sort (snd y)"
            by blast
          show "b \<or> (\<exists>y\<in>set (concat cs). inf_sort (snd y))" 
          proof (cases "(s1, Var x') \<in># mp_rx rxb \<and> (s2, Var x') \<in># mp_rx rxb")
            case True
            with ic have b unfolding b inf_var_conflict_def by blast
            thus ?thesis ..
          next
            case False
            with ic have "(s1,Var x') = (t,Var x) \<or> (s2,Var x') = (t,Var x)" by auto
            hence "\<exists> s y. (s, Var x) \<in># add_mset (t, Var x) (mp_rx rxb) \<and> Conflict_Var t s y \<and> inf_sort (snd y)" 
            proof
              assume "(s1, Var x') = (t, Var x)" 
              thus ?thesis using ic by blast
            next
              assume *: "(s2, Var x') = (t, Var x)" 
              with ic have "Conflict_Var s1 t y" by auto
              hence "Conflict_Var t s1 y" using conflicts_sym[of s1 t] by (cases "conflicts s1 t"; cases "conflicts t s1", auto)
              with ic * show ?thesis by blast
            qed
            then obtain s y where sx: "(s, Var x) \<in># add_mset (t, Var x) (mp_rx rxb)" and y: "Conflict_Var t s y" and inf: "inf_sort (snd y)" 
              by blast
            from wf have dist: "distinct (map fst rx)" unfolding wf_rx_def rxb by auto
            from y have "s \<noteq> t" by auto
            with sx have "(s, Var x) \<in># mp_rx rxb" by auto
            hence "s \<in> set ts" unfolding mp_rx_def rxb using mem eq_key_imp_eq_value[OF dist] by auto
            with y confl have "y \<in> set (concat cs)" by (cases "conflicts t s"; force)
            with inf show ?thesis by auto
          qed
        qed  
        have wf: "wf_rx rx'" using wf ts' unfolding wf_rx_def id unfolding rx' rxb snd_conv b by (auto simp: distinct_update set_update[OF look])
        show ?thesis using wf id unfolding mp by (auto simp: mp_lr_def)
      qed
    qed
  }
qed

lemma decomp_impl: "decomp_impl mp = res \<Longrightarrow> 
    (res = Some mp' \<longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) (mp_lr mp' + M) \<and> wf_lr mp')
  \<and> (res = None \<longrightarrow> (\<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp + M) mp' \<and> match_fail mp'))" 
proof (induct mp arbitrary: res M mp' rule: decomp_impl.induct)
  case 1
  thus ?case by (auto simp: mp_lr_def mp_rx_def List.maps_def wf_lr_def wf_lx_def wf_rx_def inf_var_conflict_def)
next
  case (2 f ts g ls mp res M mp')
  have id: "mp_list ((Fun f ts, Fun g ls) # mp) + M = add_mset (Fun f ts, Fun g ls) (mp_list mp + M)" 
    by auto
  show ?case 
  proof (cases "(f,length ts) = (g,length ls)")
    case False
    with 2(2-) have res: "res = None" by auto
    from match_clash[OF False, of "(mp_list mp + M)", folded id]
    show ?thesis unfolding res by blast
  next
    case True
    have id2: "mp_list (zip ts ls @ mp) + M = mp_list mp + M + mp_list (zip ts ls)" 
      by auto
    from True 2(2-) have res: "decomp_impl (zip ts ls @ mp) = res" by auto
    note IH = 2(1)[OF True this, of mp' M]
    note step = match_decompose[OF True, of "mp_list mp + M", folded id id2]
    from IH step show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
next
  case (3 x g ls mp res M mp')
  note res = 3(2)[unfolded decomp_impl.simps]
  show ?case
  proof (cases "decomp_impl mp")
    case None
    from 3(1)[OF None, of mp' "add_mset (Var x, Fun g ls) M"] None res show ?thesis by auto
  next
    case (Some mpx)
    then obtain lx rx where decomp: "decomp_impl mp = Some (lx,rx)" by (cases mpx, auto)
    from res[unfolded decomp option.simps split] have res: "res = Some ( (x, Fun g ls) # lx, rx)" by auto
    from 3(1)[OF decomp, of "(lx, rx)" "add_mset (Var x, Fun g ls) M"] res
    show ?thesis by (auto simp: mp_lr_def wf_lr_def wf_lx_def)
  qed
next
  case (4 t y mp res M mp')
  note res = 4(2)[unfolded decomp_impl.simps]
  show ?case
  proof (cases "decomp_impl mp")
    case None
    from 4(1)[OF None, of mp' "add_mset (t, Var y) M"] None res show ?thesis by auto
  next
    case (Some mpx)
    then obtain lx rx where decomp: "decomp_impl mp = Some (lx,rx)" by (cases mpx, auto)
    note res = res[unfolded decomp option.simps split]
    from 4(1)[OF decomp, of "( lx, rx)" "add_mset (t, Var y) M"]
    have IH: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list ((t, Var y) # mp) + M) (mp_lr ( lx, rx) + add_mset (t, Var y) M)"
      "wf_lr ( lx, rx)" by auto
    from IH have wf_rx: "wf_rx rx" unfolding wf_lr_def by auto
    show ?thesis 
    proof (cases "insert_rx t y rx")
      case None
      with res have res: "res = None" by auto
      from insert_rx(2)[OF None wf_rx refl refl, of lx M]
        IH res show ?thesis by auto
    next
      case (Some rx')
      with res have res: "res = Some ( lx, rx')" by auto
      from insert_rx(1)[OF Some wf_rx refl refl, of lx M]
      have wf_rx: "wf_rx rx'" 
        and steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr ( lx, rx) + add_mset (t, Var y) M) (mp_lr ( lx, rx') + M)" 
        by auto
      from IH(1) steps
      have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list ((t, Var y) # mp) + M) (mp_lr ( lx, rx') + M)" by auto
      from wf_rx IH(2-) have wf: "wf_lr ( lx, rx')"  
        unfolding wf_lr_def by auto
      from res wf steps show ?thesis by auto
    qed
  qed
qed

lemma match_var_impl: assumes wf: "wf_lr mp" 
shows "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr mp) (mp_lr (match_var_impl mp))" 
  and "wf_lr2 (match_var_impl mp)" 
proof -
  note [simp] = List.maps_def
  let ?mp' = "match_var_impl mp" 
  from assms obtain xl rx b where mp3: "mp = (xl,(rx,b))" by (cases mp, auto)
  define xs where "xs = remdups (List.maps (vars_term_list o snd) xl)" 
  have xs: "xl = [] \<Longrightarrow> xs = []" unfolding xs_def by auto
  define f where "f = (\<lambda> (x,ts :: ('f, nat \<times> 's)term list). tl ts \<noteq> [] \<or> x \<in> set xs)" 
  define mp' where "mp' = mp_rx (filter f rx, b) + mp_list (mp_lx xl)" 
  define deleted where "deleted = mp_rx (filter (Not o f) rx, b)" 
  have mp': "mp_lr ?mp' = mp'" "?mp' = (xl, (filter f rx,b))" 
    unfolding mp3 mp'_def match_var_impl_def split xs_def f_def mp_lr_def by auto
  have "mp_rx (rx,b) = mp_rx (filter f rx, b) + mp_rx (filter (Not o f) rx, b)" 
    unfolding mp_rx_def List.maps_def by (induct rx, auto)
  hence mp: "mp_lr mp = deleted + mp'" unfolding mp3 mp_lr_def mp'_def deleted_def by auto
  have "inf_var_conflict (mp_mset (mp_rx (filter f rx, b))) = inf_var_conflict (mp_mset (mp_rx (rx, b)))" (is "?ivcf = ?ivc")
  proof
    show "?ivcf \<Longrightarrow> ?ivc" unfolding inf_var_conflict_def mp_rx_def fst_conv List.maps_def by force
    assume ?ivc 
    from this[unfolded inf_var_conflict_def]
    obtain s t x y where s: "(s, Var x) \<in># mp_rx (rx, b)" and t: "(t, Var x) \<in># mp_rx (rx, b)" and c: "Conflict_Var s t y" and inf: "inf_sort (snd y)" 
      by blast
    from c conflicts(5)[of s t] have st: "s \<noteq> t" by auto
    from s[unfolded mp_rx_def List.maps_def]
    obtain ss where xss: "(x,ss) \<in> set rx" and s: "s \<in> set ss" by auto
    from t[unfolded mp_rx_def List.maps_def]
    obtain ts where xts: "(x,ts) \<in> set rx" and t: "t \<in> set ts" by auto
    from wf[unfolded mp3 wf_lr_def wf_rx_def] have "distinct (map fst rx)" by auto
    from eq_key_imp_eq_value[OF this xss xts] t have t: "t \<in> set ss" by auto
    with s st have "f (x,ss)" unfolding f_def by (cases ss; cases "tl ss"; auto)
    hence "(x, ss) \<in> set (filter f rx)" using xss by auto
    with s t have "(s, Var x) \<in># mp_rx (filter f rx, b)" "(t, Var x) \<in># mp_rx (filter f rx, b)"
      unfolding mp_rx_def List.maps_def by auto
    with c inf 
    show ?ivcf unfolding inf_var_conflict_def by blast
  qed        
  also have "\<dots> = b" using wf unfolding mp3 wf_lr_def wf_rx_def by auto
  finally have ivcf: "?ivcf = b" .
  show "wf_lr2 (match_var_impl mp)" 
  proof (cases "xl = []")
    case False
    from ivcf False wf[unfolded mp3] show ?thesis
      unfolding mp' wf_lr2_def wf_lr_def split wf_rx_def by (auto simp: distinct_map_filter)
  next
    case True
    with xs have "xs = []" by auto
    with True wf[unfolded mp3]
    show ?thesis
      unfolding wf_lr2_def mp' split wf_rx2_def wf_rx_def ivcf
      unfolding mp' wf_lr2_def wf_lr_def split wf_rx_def wf_rx2_def wf_ts_def wf_ts2_def f_def 
      apply (clarsimp simp: distinct_map_filter)
      subgoal for x ts by (cases ts; cases "tl ts"; force)
      done
  qed
  {
    fix xt t
    assume del: "(t, xt) \<in># deleted" 
    from this[unfolded deleted_def mp_rx_def, simplified]
    obtain x ts where mem: "(x,ts) \<in> set rx" and nf: "\<not> f (x, ts)" and t: "t \<in> set ts" and xt: "xt = Var x" by force
    note del = del[unfolded xt]
    from nf[unfolded f_def split] t have xxs: "x \<notin> set xs" and ts: "ts = [t]" by (cases ts; cases "tl ts", auto)+
    from split_list[OF mem[unfolded ts]] obtain rx1 rx2 where rx: "rx = rx1 @ (x,[t]) # rx2" by auto
    from wf[unfolded wf_lr_def mp3] have wf: "wf_rx (rx,b)" by auto
    hence "distinct (map fst rx)" unfolding wf_rx_def by auto  
    with rx have xrx: "x \<notin> fst ` set rx1 \<union> fst ` set rx2" by auto
    define mp'' where "mp'' = mp_rx (filter (Not \<circ> f) (rx1 @ rx2), b)" 
    have eq: "deleted = add_mset (t, Var x) mp''" 
      unfolding deleted_def mp''_def rx mp_rx_def List.maps_def mset_concat_union using nf ts by auto
    have "\<exists> x mp''. xt = Var x \<and> deleted = add_mset (t, Var x) mp'' \<and> x \<notin> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
    proof (intro exI conjI, rule xt, rule eq, intro notI)
      assume "x \<in> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
      then obtain s t' where st: "(s,t') \<in> mp_mset (mp' + mp'')" and xt: "x \<in> vars t'" by force
      from xrx have "(s,t') \<notin> mp_mset mp''" using xt unfolding mp''_def mp_rx_def by force
      with st have "(s,t') \<in> mp_mset mp'" by auto
      with xxs have "(s, t') \<in># mp_rx (filter f rx, b)" using xt unfolding xs_def mp'_def mp_rx_def
        by auto
      with xt nf show False unfolding mp_rx_def f_def split ts list.sel 
        by auto (metis Un_iff \<open>\<not> (tl ts \<noteq> [] \<or> x \<in> set xs)\<close> fst_conv image_eqI prod.inject rx set_ConsD set_append ts xrx)
    qed
  } note lin_vars = this
  show "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_lr mp) (mp_lr (match_var_impl mp))" unfolding mp mp'(1) using lin_vars
  proof (induct deleted)
    case (add pair deleted)
    obtain t xt where pair: "pair = (t,xt)" by force
    hence "(t,xt) \<in># add_mset pair deleted" by auto
    from add(2)[OF this] pair
    obtain x where "add_mset pair deleted + mp' = add_mset (t, Var x) (deleted + mp')" 
      and x: "x \<notin> \<Union> (vars ` snd ` (mp_mset (deleted + mp')))" 
      and pair: "pair = (t, Var x)" 
      by auto  
    from match_match[OF this(2), of t, folded this(1)]
    have one: "add_mset pair deleted + mp' \<rightarrow>\<^sub>m (deleted + mp')" .
    have two: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (deleted + mp') mp'" 
    proof (rule add(1), goal_cases)
      case (1 s yt)
      hence "(s,yt) \<in># add_mset pair deleted" by auto
      from add(2)[OF this]
      obtain y mp'' where yt: "yt = Var y" "add_mset pair deleted = add_mset (s, Var y) mp''"
         "y \<notin> \<Union> (vars ` snd ` (mp_mset mp'' \<union> mp_mset mp'))" 
        by auto
      from 1[unfolded yt] have "y \<in> \<Union> (vars ` snd ` (mp_mset (deleted + mp')))" by force
      with x have "x \<noteq> y" by auto
      with pair yt have "pair \<noteq> (s,Var y)" by auto
      with yt(2) have del: "deleted = add_mset (s, Var y) (mp'' - {#pair#})"
        by (meson add_eq_conv_diff)
      show ?case 
        by (intro exI conjI, rule yt, rule del, rule contra_subsetD[OF _ yt(3)]) 
         (intro UN_mono, auto dest: in_diffD)
    qed
    from one two show ?case by auto
  qed auto
qed

lemma match_steps_impl: assumes "match_steps_impl mp = res" 
  shows "res = Some mp' \<Longrightarrow> (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp') \<and> wf_lr2 mp'" 
    and "res = None \<Longrightarrow> \<exists> mp'. (\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp' \<and> match_fail mp'" 
proof (atomize (full), goal_cases)
  case 1
  obtain res' where decomp: "decomp_impl mp = res'" by auto
  note res = assms[unfolded match_steps_impl_def decomp]
  note decomp = decomp_impl[OF decomp, of _ "{#}", unfolded empty_neutral]
  show ?case
  proof (cases res')
    case None
    with decomp res show ?thesis by auto
  next
    case (Some mp'')
    with decomp[of mp'']
    have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp'')" and wf: "wf_lr mp''" by auto
    from res[unfolded Some] have res: "res = Some (match_var_impl mp'')" by auto
    from match_var_impl[OF wf] steps res show ?thesis by auto
  qed
qed

lemma pat_inner_impl: assumes "pat_inner_impl p pd = res" 
  and "wf_pat_lr pd" 
  and "tvars_pp (pat_mset (pat_mset_list p + pat_lr pd)) \<subseteq> V" 
  shows "res = None \<Longrightarrow> (add_mset (pat_mset_list p + pat_lr pd) P, P) \<in> \<Rrightarrow>\<^sup>+" 
    and "res = Some p' \<Longrightarrow> (add_mset (pat_mset_list p + pat_lr pd) P, add_mset (pat_lr p') P) \<in> \<Rrightarrow>\<^sup>*
             \<and> wf_pat_lr p' \<and> tvars_pp (pat_mset (pat_lr p')) \<subseteq> V" 
proof (atomize(full), insert assms, induct p arbitrary: pd res p')
  case Nil
  then show ?case by (auto simp: wf_pat_lr_def pat_mset_list_def pat_lr_def)
next
  case (Cons mp p pd res p')
  let ?p = "pat_mset_list p + pat_lr pd" 
  have id: "pat_mset_list (mp # p) + pat_lr pd = add_mset (mp_list mp) ?p" unfolding pat_mset_list_def by auto  
  show ?case
  proof (cases "match_steps_impl mp")
    case (Some mp')
    from match_steps_impl(1)[OF Some refl]
    have steps: "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) (mp_lr mp')" and wf: "wf_lr2 mp'" by auto
    have id2: "pat_mset_list p + pat_lr (mp' # pd) = add_mset (mp_lr mp') ?p" unfolding pat_lr_def by auto
    from mp_step_mset_steps_vars[OF steps] Cons(4) 
    have vars: "tvars_pp (pat_mset (pat_mset_list p + pat_lr (mp' # pd))) \<subseteq> V"
        unfolding id2 by (auto simp: tvars_pp_def pat_mset_list_def)
    note steps = mp_step_mset_cong[OF steps, of ?p P, folded id]
    note res = Cons(2)[unfolded pat_inner_impl.simps Some option.simps]
    show ?thesis 
    proof (cases "empty_lr mp'")
      case False
      with Cons(3) wf have wf: "wf_pat_lr (mp' # pd)" unfolding wf_pat_lr_def by auto
      from res False have "pat_inner_impl p (mp' # pd) = res" by auto
      from Cons(1)[OF this wf, of p', OF vars, unfolded id2] steps
      show ?thesis by auto
    next
      case True
      with wf have id3: "mp_lr mp' = {#}" unfolding wf_lr2_def empty_lr_def by (cases mp', auto simp: mp_lr_def mp_rx_def List.maps_def)
      from True res have res: "res = None" by auto
      have "(add_mset (add_mset (mp_lr mp') ?p) P, P) \<in> P_step" 
        unfolding id3 P_step_def using P_simp_pp[OF pat_remove_pp[of ?p], of P] by auto
      with res steps show ?thesis by auto
    qed
  next
    case None
    from match_steps_impl(2)[OF None refl] obtain mp' where
      "(\<rightarrow>\<^sub>m)\<^sup>*\<^sup>* (mp_list mp) mp'" and fail: "match_fail mp'" by auto
    note steps = mp_step_mset_cong[OF this(1), of ?p P, folded id]
    from P_simp_pp[OF pat_remove_mp[OF fail, of ?p], of P]
    have "(add_mset (add_mset mp' ?p) P, add_mset ?p P) \<in> P_step" 
      unfolding P_step_def by auto
    with steps have steps: "(add_mset (pat_mset_list (mp # p) + pat_lr pd) P, add_mset ?p P) \<in> P_step^*" by auto
    note res = Cons(2)[unfolded pat_inner_impl.simps None option.simps] 
    have vars: "tvars_pp (pat_mset (pat_mset_list p + pat_lr pd)) \<subseteq> V" 
      using Cons(4) unfolding tvars_pp_def pat_mset_list_def by auto
    from Cons(1)[OF res Cons(3), of p', OF vars] steps
    show ?thesis by auto
  qed
qed

lemma pat_mset_list: "pat_mset (pat_mset_list p) = pat_list p" 
  unfolding pat_list_def pat_mset_list_def by (auto simp: image_comp)

text \<open>Main simulation lemma for a single @{const pat_impl} step.\<close>
lemma pat_impl: assumes "pat_impl n p = res" 
    and vars: "fst ` tvars_pp (pat_list p) \<subseteq> {..<n}" 
  shows "res = None \<Longrightarrow> \<exists> p'. (add_mset (pat_mset_list p) P, add_mset p' P) \<in> \<Rrightarrow>\<^sup>* \<and> pat_fail p'" 
    and "res = Some ps \<Longrightarrow> (add_mset (pat_mset_list p) P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>\<^sup>+
             \<and> fst ` tvars_pp (\<Union> (pat_list ` set ps)) \<subseteq> {..<n+m}" 
proof (atomize(full), goal_cases)
  case 1
  have wf: "wf_pat_lr []" unfolding wf_pat_lr_def by auto
  have "fst ` tvars_pp (pat_mset (pat_mset_list p)) \<subseteq> {..<n}" 
    using vars unfolding pat_mset_list .
  hence vars: "tvars_pp (pat_mset (pat_mset_list p)) \<subseteq> {..<n} \<times> UNIV" by force
  have "pat_mset_list p + pat_lr [] = pat_mset_list p" unfolding pat_lr_def by auto
  note pat_inner = pat_inner_impl[OF refl wf, of p, unfolded this, OF vars]
  note res = assms(1)[unfolded pat_impl_def]
  show ?case
  proof (cases "pat_inner_impl p []")
    case None
    from pat_inner(1)[OF this, of P] res[unfolded None option.simps] vars
    show ?thesis by (auto simp: tvars_pp_def)
  next
    case (Some p')
    from pat_inner(2)[OF this, of P]
    have steps: "(add_mset (pat_mset_list p) P, add_mset (pat_lr p') P) \<in> \<Rrightarrow>\<^sup>*" and wf: "wf_pat_lr p'"
      and varsp': "tvars_pp (pat_mset (pat_lr p')) \<subseteq> {..<n} \<times> UNIV" by auto
    note res = res[unfolded Some option.simps]
    show ?thesis
    proof (cases "\<forall>mp\<in>set p'. snd (snd mp)")
      case True
      with res have res: "res = None" by auto
      have "pat_fail (pat_lr p')" 
      proof (intro pat_failure' ballI)
        fix mps
        assume "mps \<in> pat_mset (pat_lr p')" 
        then obtain mp where mem: "mp \<in> set p'" and mps: "mps = mp_mset (mp_lr mp)" by (auto simp: pat_lr_def)
        obtain lx rx b where mp: "mp = (lx,rx,b)" by (cases mp, auto)
        from mp mem True have b by auto
        with wf[unfolded wf_pat_lr_def, rule_format, OF mem, unfolded wf_lr2_def mp split]
        have "inf_var_conflict (set_mset (mp_rx (rx,b)))" unfolding wf_rx_def wf_rx2_def by (auto split: if_splits)
        thus "inf_var_conflict mps" unfolding mps mp_lr_def mp split
          unfolding inf_var_conflict_def by fastforce
      qed
      with steps res
      show ?thesis by auto
    next
      case False
      define p'l where "p'l = map mp_lr_list p'" 
      define x where "x = find_var p'" 
      define ps where "ps = map (\<lambda>\<tau>. subst_pat_problem_list \<tau> p'l) (\<tau>s_list n x)" 
      have id: "pat_lr p' = pat_mset_list p'l" unfolding pat_mset_list_def pat_lr_def p'l_def map_map o_def
        by (intro arg_cong[of _ _ mset] map_cong refl, auto simp: mp_lr_def mp_lr_list_def mp_rx_def mp_rx_list_def)
      from False have "(\<forall>mp\<in>set p'. snd (snd mp)) = False" by auto
      from res[unfolded this if_False Let_def, folded p'l_def x_def, folded ps_def]
      have res: "res = Some ps" by auto
      have step: "(add_mset (pat_lr p') P, mset (map pat_mset_list ps) + P) \<in> \<Rrightarrow>" 
        unfolding P_step_def 
      proof (standard, unfold split, intro P_simp_pp)
        note x = x_def[unfolded find_var_def]
        let ?concat = "concat (map (\<lambda> (lx,_). lx) p')" 
        have disj: "tvars_disj_pp {n..<n + m} (pat_mset (pat_lr p'))" 
          using varsp' unfolding tvars_pp_def tvars_disj_pp_def tvars_mp_def by force
        have subst: "map (\<lambda>\<tau>. subst_pat_problem_mset \<tau> (pat_lr p')) (\<tau>s_list n x) = map pat_mset_list ps" 
          unfolding id
          unfolding ps_def subst_pat_problem_list_def subst_pat_problem_mset_def subst_match_problem_mset_def
            subst_match_problem_list_def map_map o_def
          by (intro list.map_cong0, auto simp: pat_mset_list_def o_def image_mset.compositionality)
        show "pat_lr p' \<Rightarrow>\<^sub>m mset (map pat_mset_list ps)" 
        proof (cases ?concat)
          case (Cons pair list)
          with x obtain t where concat: "?concat = (x,t) # list" by (cases pair, auto)
          hence "(x,t) \<in> set ?concat" by auto
          then obtain mp where "mp \<in> set p'" and "(x,t) \<in> set ((\<lambda> (lx,_). lx) mp)" by auto
          then obtain lx rx where mem: "(lx,rx) \<in> set p'" and xt: "(x,t) \<in> set lx" by auto
          from wf mem have wf: "wf_lx lx" unfolding wf_pat_lr_def wf_lr2_def by auto
          with xt have t: "is_Fun t" unfolding wf_lx_def by auto
          from mem obtain p'' where pat: "pat_lr p' = add_mset (mp_lr (lx,rx)) p''" 
            unfolding pat_lr_def by simp (metis in_map_mset mset_add set_mset_mset)
          from xt have xt: "(Var x, t) \<in># mp_lr (lx,rx)" unfolding mp_lr_def by force
          from pat_instantiate[OF _ disjI1[OF conjI[OF xt t]], of n p'', folded pat, OF disj]
          show ?thesis unfolding subst .
        next
          case Nil
          let ?fp = "filter (Not \<circ> snd \<circ> snd) p'" 
          from False have "set ?fp \<noteq> {}" unfolding o_def filter_empty_conv set_empty
            by auto
          then obtain mp p'' where fp: "?fp = mp # p''" by (cases ?fp) auto
          obtain lx rx b where mp: "mp = (lx,rx,b)" by (cases mp) auto
          have mpp: "mp \<in> set p'" using arg_cong[OF fp, of set] by auto
          from mp mpp Nil have lx: "lx = []" by auto
          from fp have "(lx,rx,b) \<in> set ?fp" unfolding mp by auto
          hence "\<not> b" unfolding o_def by auto
          with mp lx have mp: "mp = ([],rx,False)" by auto
          from wf mpp have wf: "wf_lr2 mp" and ne: "\<not> empty_lr mp"  unfolding wf_pat_lr_def by auto
          from wf[unfolded wf_lr2_def mp split] mp
          have wf: "wf_rx2 (rx, False)" and mp: "mp = ([],rx,False)" by auto
          from ne[unfolded empty_lr_def mp split] obtain y ts rx' 
            where rx: "rx = (y,ts) # rx'" by (cases rx, auto)
          from wf[unfolded wf_rx2_def] have ninf: "\<not> inf_var_conflict (mp_mset (mp_rx (rx, False)))" 
            and wf: "wf_ts2 ts" unfolding rx by auto   
          from wf[unfolded wf_ts2_def] obtain s t ts' where ts: "ts = s # t # ts'" and 
            diff: "s \<noteq> t" and conf: "conflicts s t \<noteq> None" 
            by (cases ts; cases "tl ts", auto)
          from conf obtain xs where conf: "conflicts s t = Some xs" by (cases "conflicts s t", auto)
          with conflicts(5)[of s t] diff have "xs \<noteq> []" by auto          
          with x[unfolded Nil list.simps fp list.sel mp split Let_def rx ts conf option.sel]
          obtain xs' where xs: "xs = x # xs'" by (cases xs) auto
          from conf xs have confl: "Conflict_Var s t x" by auto
          from ts rx have sty: "(s, Var y) \<in># mp_rx (rx, False)" "(t, Var y) \<in># mp_rx (rx,False)" 
            by (auto simp: mp_rx_def List.maps_def)
          with confl ninf have "\<not> inf_sort (snd x)" unfolding inf_var_conflict_def by blast
          with sty confl rx have main: "(s, Var y) \<in># mp_lr mp \<and> (t, Var y) \<in># mp_lr mp \<and> Conflict_Var s t x \<and> \<not> inf_sort (snd x)" 
            unfolding mp by (auto simp: mp_lr_def)
          from mpp obtain p'' where pat: "pat_lr p' = add_mset (mp_lr mp) p''" 
            unfolding pat_lr_def by simp (metis in_map_mset mset_add set_mset_mset)
          from pat_instantiate[OF _ disjI2[OF main], of n p'', folded pat, OF disj]
          show ?thesis unfolding subst .
        qed
      qed
      have "fst ` tvars_pp (\<Union> (pat_list ` set ps)) \<subseteq> {..<n + m}"
      proof
        fix yn
        assume "yn \<in> fst ` tvars_pp (\<Union> (pat_list ` set ps))" 
        then obtain pi y mp where pi: "pi \<in> set ps" and mp: "mp \<in> set pi" and y: "y \<in> tvars_mp (set mp)" and yn: "yn = fst y" 
          unfolding tvars_pp_def pat_list_def by force
        from pi[unfolded ps_def set_map subst_pat_problem_list_def subst_match_problem_list_def, simplified] 
        obtain \<tau> where tau: "\<tau> \<in> set (\<tau>s_list n x)" and pi: "pi = map (map (subst_left \<tau>)) p'l" by auto
        from tau[unfolded \<tau>s_list_def]
        obtain info where "info \<in> set (Cl (snd x))" and tau: "\<tau> = \<tau>c n x info" by auto
        from Cl_len[of "snd x"] this(1) have len: "length (snd info) \<le> m" by force
        from mp[unfolded pi set_map] obtain mp' where mp': "mp' \<in> set p'l" and mp: "mp = map (subst_left \<tau>) mp'" by auto
        from y[unfolded mp tvars_mp_def image_comp o_def set_map]
        obtain pair where *: "pair \<in> set mp'" "y \<in> vars (fst (subst_left \<tau> pair))" by auto
        obtain s t where pair: "pair = (s,t)" by force
        from *[unfolded pair] have st: "(s,t) \<in> set mp'" and y: "y \<in> vars (s \<cdot> \<tau>)" unfolding subst_left_def by auto
        from y[unfolded vars_term_subst, simplified] obtain z where z: "z \<in> vars s" and y: "y \<in> vars (\<tau> z)" by auto
        obtain f ss where info: "info = (f,ss)" by (cases info, auto)
        with len have len: "length ss \<le> m" by auto
        define ts :: "('f,_)term list" where "ts = map Var (zip [n..<n + length ss] ss)" 
        from tau[unfolded \<tau>c_def info split] have tau: "\<tau> = subst x (Fun f ts)"  unfolding ts_def by auto
        have "fst ` vars (Fun f ts) \<subseteq> {..< n + length ss}" unfolding ts_def by (auto simp: set_zip)
        also have "\<dots> \<subseteq> {..< n + m}" using len by auto
        finally have subst: "fst ` vars (Fun f ts) \<subseteq> {..< n + m}" by auto
        show "yn \<in> {..<n + m}" 
        proof (cases "z = x")
          case True
          with y subst tau yn show ?thesis by auto
        next
          case False
          hence "\<tau> z = Var z" unfolding tau by (auto simp: subst_def)
          with y have "z = y" by auto
          with z have y: "y \<in> vars s" by auto
          with st have "y \<in> tvars_mp (set mp')" unfolding tvars_mp_def by force
          with mp' have "y \<in> tvars_pp (set ` set p'l)" unfolding tvars_pp_def by auto
          also have "\<dots> = tvars_pp (pat_mset (pat_mset_list p'l))" 
            by (rule arg_cong[of _ _ tvars_pp], auto simp: pat_mset_list_def image_comp)
          also have "\<dots> = tvars_pp (pat_mset (pat_lr p'))" unfolding id[symmetric] by simp
          also have "\<dots> \<subseteq> {..<n} \<times> UNIV" using varsp' .
          finally show ?thesis using yn by auto
        qed
      qed
      with step steps res show ?thesis by auto
    qed
  qed
qed

text \<open>The simulation property for @{const pats_impl}, proven by induction
  on the terminating relation of the multiset-implementation.\<close>
lemma pats_impl_P_step: assumes "Ball (set ps) (\<lambda> p. fst ` tvars_pp (pat_list p) \<subseteq> {..<n})" 
  shows 
    \<comment> \<open>if result is True, then one can reach empty set\<close>
    "pats_impl n ps \<Longrightarrow> (pats_mset_list ps, {#}) \<in> \<Rrightarrow>\<^sup>*" 
    \<comment> \<open>if result is False, then one can reach bottom\<close>
    "\<not> pats_impl n ps \<Longrightarrow> (pats_mset_list ps, bottom_mset) \<in> \<Rrightarrow>\<^sup>*" 
proof (atomize(full), insert assms, induct ps arbitrary: n rule: SN_induct[OF SN_inv_image[OF SN_imp_SN_trancl[OF SN_P_step]], of pats_mset_list])
  case (1 ps n)
  show ?case 
  proof (cases ps)
    case Nil
    show ?thesis unfolding pats_impl.simps[of n ps] unfolding Nil by auto
  next
    case (Cons p ps1)
    hence id: "pats_mset_list ps = add_mset (pat_mset_list p) (pats_mset_list ps1)" by auto
    note res = pats_impl.simps[of n ps, unfolded Cons list.simps, folded Cons]
    from 1(2)[rule_format, of p] Cons have "fst ` tvars_pp (pat_list p) \<subseteq> {..<n}" by auto
    note pat_impl = pat_impl[OF refl this]
    show ?thesis
    proof (cases "pat_impl n p")
      case None
      with res have res: "pats_impl n ps = False" by auto
      from pat_impl(1)[OF None, of "pats_mset_list ps1", folded id]  
      obtain p' where steps: "(pats_mset_list ps, add_mset p' (pats_mset_list ps1)) \<in> \<Rrightarrow>\<^sup>*" and fail: "pat_fail p'" 
        by auto
      show ?thesis
      proof (cases "add_mset p' (pats_mset_list ps1) = bottom_mset")
        case True
        with res steps show ?thesis by auto
      next
        case False
        from P_failure[OF fail False] 
        have "(add_mset p' (pats_mset_list ps1), bottom_mset) \<in> \<Rrightarrow>" unfolding P_step_def by auto
        with steps res show ?thesis by simp
      qed
    next
      case (Some ps2)
      with res have res: "pats_impl n ps = pats_impl (n + m) (ps2 @ ps1)" by auto
      from pat_impl(2)[OF Some, of "pats_mset_list ps1", folded id]
      have steps: "(pats_mset_list ps, mset (map pat_mset_list (ps2 @ ps1))) \<in> \<Rrightarrow>\<^sup>+" 
          and vars: "fst ` tvars_pp (\<Union> (pat_list ` set ps2)) \<subseteq> {..<n + m}" by auto
      hence rel: "(ps, ps2 @ ps1) \<in> inv_image (P_step\<^sup>+) pats_mset_list" by auto
      have vars: "\<forall>p\<in>set (ps2 @ ps1). fst ` tvars_pp (pat_list p) \<subseteq> {..<n + m}"
      proof 
        fix p
        assume "p \<in> set (ps2 @ ps1)" 
        hence "p \<in> set ps2 \<or> p \<in> set ps1" by auto
        thus "fst ` tvars_pp (pat_list p) \<subseteq> {..<n + m}" 
        proof
          assume "p \<in> set ps2" 
          hence "fst ` tvars_pp (pat_list p) \<subseteq> fst ` tvars_pp (\<Union> (pat_list ` set ps2))" 
            unfolding tvars_pp_def by auto
          with vars show ?thesis by auto
        next
          assume "p \<in> set ps1" 
          hence "p \<in> set ps" unfolding Cons by auto
          from 1(2)[rule_format, OF this] show ?thesis by auto
        qed
      qed
      show ?thesis using 1(1)[OF rel vars] steps unfolding res[symmetric] by auto
    qed
  qed
qed


text \<open>Consequence: partial correctness of the list-based implementation on well-formed inputs\<close>

theorem pats_impl: assumes wf: "\<forall>pp \<in> pat_list ` set P. wf_pat pp" 
  and n: "\<forall>p\<in>set P. fst ` tvars_pp (pat_list p) \<subseteq> {..<n}" 
  shows "pats_impl n P \<longleftrightarrow> pats_complete (pat_list ` set P)" 
proof - 
  from wf have wf: "wf_pats (pat_list ` set P)" by (auto simp: wf_pats_def)
  have id: "pats_mset (pats_mset_list P) = pat_list ` set P" unfolding pat_list_def 
    by (auto simp: pat_mset_list_def image_comp)
  {
    assume "pats_impl n P" 
    from pats_impl_P_step(1)[OF n this]
    have "(pats_mset_list P, {#}) \<in> \<Rrightarrow>\<^sup>*" by auto
    from P_steps_pcorrect[OF _ this, unfolded id, OF wf]
    have "pats_complete (pat_list ` set P)" by auto
  }
  moreover
  {
    assume "\<not> pats_impl n P" 
    from pats_impl_P_step(2)[OF n this]
    have "(pats_mset_list P, {#{#}#}) \<in> \<Rrightarrow>\<^sup>*" by auto
    from P_steps_pcorrect[OF _ this, unfolded id, OF wf]
    have "\<not> pats_complete (pat_list ` set P)" by auto
  }
  ultimately show ?thesis by auto
qed 

corollary pat_complete_impl: 
  assumes wf: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> S" 
  shows "pat_complete_impl P \<longleftrightarrow> pats_complete (pat_list ` set P)" 
proof - 
  have wf: "Ball (pat_list ` set P) wf_pat" 
    unfolding pat_list_def wf_pat_def wf_match_def tvars_mp_def using wf[unfolded set_concat image_comp] by force
  let ?l = "(List.maps (map fst o vars_term_list o fst) (concat (concat P)))" 
  define n where "n = Suc (max_list ?l)" 
  have n: "\<forall>p\<in>set P. fst ` tvars_pp (pat_list p) \<subseteq> {..<n}" 
  proof (intro ballI subsetI)
    fix p x
    assume "p \<in> set P" and "x \<in> fst ` tvars_pp (pat_list p)" 
    hence "x \<in> set ?l" unfolding List.maps_def tvars_pp_def tvars_mp_def pat_list_def 
      by force
    from max_list[OF this] have "x < n" unfolding n_def by auto
    thus "x \<in> {..<n}" by auto
  qed  
  have "pat_complete_impl P = pats_impl n P" 
    unfolding pat_complete_impl_def n_def Let_def ..
  from pats_impl[OF wf n, folded this]
  show ?thesis .
qed
end 

subsection \<open>Getting the result outside the locale with assumptions\<close>

text \<open>We next lift the results for the list-based implementation out of the locale.
  Here, we use the existing algorithms to decide non-empty sorts @{const decide_nonempty_sorts} 
  and to compute the infinite sorts @{const compute_inf_sorts}.\<close>

context pattern_completeness_context
begin
lemma pat_complete_impl_wrapper: assumes C_Cs: "C = map_of Cs" 
  and dist: "distinct (map fst Cs)" 
  and inhabited: "decide_nonempty_sorts Sl Cs = None"   
  and S_Sl: "S = set Sl" 
  and inf_sort: "inf_sort = (\<lambda> s. s \<in> compute_inf_sorts Cs)" 
  and C: "\<And> f \<sigma>s \<sigma>. ((f,\<sigma>s),\<sigma>) \<in> set Cs \<Longrightarrow> length \<sigma>s \<le> m \<and> set (\<sigma> # \<sigma>s) \<subseteq> S" 
  and Cl: "\<And> s. Cl s = map fst (filter ((=) s o snd) Cs)" 
  and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> S" 
  shows "pat_complete_impl P = pats_complete (pat_list ` set P)" 
proof -
  from decide_nonempty_sorts(1)[OF dist C_Cs[symmetric] inhabited, folded S_Sl]
  have S: "\<And> \<sigma>. \<sigma>  \<in> S \<Longrightarrow> \<exists>t. t : \<sigma> in \<T>(C,EMPTY)"
    "\<And> \<sigma>. \<sigma>  \<in> S \<Longrightarrow> \<exists>t. t : \<sigma> in \<T>(C,EMPTYn)" unfolding EMPTY_def EMPTYn_def by auto
  {
    fix f ss s
    assume "f : ss \<rightarrow> s in C"
    hence "((f,ss),s) \<in> set Cs" unfolding C_Cs by (auto dest!: fun_hastypeD map_of_SomeD)
    from C[OF this] have "insert s (set ss) \<subseteq> S" "length ss \<le> m" by auto
  } note Cons = this
  {
    fix f ss s
    assume "(f,ss) \<in> set (Cl s)" 
    hence "((f,ss),s) \<in> set Cs" unfolding Cl by auto
    from C[OF this] have "length ss \<le> m" by auto
  }
  hence m: "\<forall>a\<in>length ` snd ` set (Cl s). a \<le> m" for s by auto
  have En: "EMPTYn = \<emptyset>" unfolding EMPTYn_def by auto
  have "\<forall>f ss s s'. f : ss \<rightarrow> s in C \<longrightarrow> s' \<in> set ss \<longrightarrow> (\<exists>t. t : s' in \<T>(C,EMPTYn))" 
  proof (intro allI impI)
    fix f ss s s'
    assume "f : ss \<rightarrow> s in C" and "s' \<in> set ss" 
    hence "s' \<in> S" using Cons(1)[of f ss s] by auto
    from S[OF this] show "\<exists>t. t : s' in \<T>(C,EMPTYn)" by auto
  qed
  from compute_inf_sorts[OF En C_Cs this dist] inf_sort
  have inf_sort: "inf_sort s = (\<not> bdd_above (size ` {t. t : s in \<T>(C,EMPTYn)}))" for s unfolding inf_sort by auto
  have Cl: "set (Cl s) = {(f,ss). f : ss \<rightarrow> s in C}" for s
    unfolding Cl set_map o_def C_Cs using dist
    by (force simp: fun_hastype_def)
  interpret pattern_completeness_context_with_assms
    apply unfold_locales
    subgoal by (rule S(1))
    subgoal by (rule Cons)
    subgoal by (rule Cons)
    subgoal by (rule inf_sort)
    subgoal by (rule Cl)
    subgoal by (rule m)
    done
  show ?thesis by (rule pat_complete_impl[OF P])
qed
end

text \<open>Next we are also leaving the locale that fixed the common parameters,
  and chooses suitable values.\<close> 

text \<open>extract all sorts from a ssignature (input and target sorts)\<close>
definition sorts_of_ssig_list :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> 's list" where
  "sorts_of_ssig_list Cs = remdups (List.maps (\<lambda> ((f,ss),s). s # ss) Cs)" 

definition decide_pat_complete :: "(('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "decide_pat_complete Cs P = (let Sl = sorts_of_ssig_list Cs;
      m = max_list (map (length o snd o fst) Cs);
      Cl = (\<lambda> s. map fst (filter ((=) s \<circ> snd) Cs)); 
      IS = compute_inf_sorts Cs
     in pattern_completeness_context.pat_complete_impl m Cl (\<lambda> s. s \<in> IS)) P" 

abbreviation (input) pat_complete where 
  "pat_complete \<equiv> pattern_completeness_context.pat_complete"

abbreviation (input) pats_complete where 
  "pats_complete \<equiv> pattern_completeness_context.pats_complete" 

text \<open>Finally: a pattern completeness decision procedure for arbitrary inputs,
  assuming sensible inputs\<close>
theorem decide_pat_complete: assumes C_Cs: "C = map_of Cs" 
  and dist: "distinct (map fst Cs)" 
  and non_empty_sorts: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None" 
  and S: "S = set (sorts_of_ssig_list Cs)"
  and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> S"
shows "decide_pat_complete Cs P = pats_complete S C  (pat_list ` set P)" 
  unfolding decide_pat_complete_def Let_def
proof (rule pattern_completeness_context.pat_complete_impl_wrapper[OF C_Cs dist non_empty_sorts S refl _ refl P])
  fix f \<sigma>s \<sigma>
  assume mem: "((f, \<sigma>s), \<sigma>) \<in> set Cs" 
  hence "length \<sigma>s \<in> set (map (length \<circ> snd \<circ> fst) Cs)" by force
  from max_list[OF this] mem
  show "length \<sigma>s \<le> max_list (map (length \<circ> snd \<circ> fst) Cs) \<and> set (\<sigma> # \<sigma>s) \<subseteq> S" 
    unfolding S sorts_of_ssig_list_def List.maps_def by force
qed

end