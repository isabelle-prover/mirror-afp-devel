theory IDL_Solver
  imports Pattern_Completeness_List
    "HOL-Library.RBT_Mapping" (* required for executability *)
    "HOL-Library.List_Lexorder"
    "HOL-Library.Product_Lexorder"
begin

type_synonym ('v,'s)idl_input = "(('v \<times> 's) \<times> int) list \<times> (('v \<times> 's) \<times> 'v \<times> 's) list list" 

definition idl_input :: "('v,'s)idl_input \<Rightarrow> bool" where 
  "idl_input = (\<lambda> (bnds, diffs).
     distinct (map fst bnds) \<and> (\<forall> v w u. (v,w) \<in> set (concat diffs) \<longrightarrow> u \<in> {v,w} \<longrightarrow> u \<in> fst ` set bnds) 
     \<and> (\<forall> v w. (v,w) \<in> set (concat diffs) \<longrightarrow> snd v = snd w) 
     \<and> (\<forall> v w. (v,w) \<in> set (concat diffs) \<longrightarrow> v \<noteq> w) 
     \<and> (\<forall> v w b1 b2. (v,b1) \<in> set bnds \<longrightarrow> (w,b2) \<in> set bnds \<longrightarrow> snd v = snd w \<longrightarrow> b1 = b2) 
     \<and> (\<forall> v b. (v,b) \<in> set bnds \<longrightarrow> b \<ge> 0))" 

definition idl_solvable :: "('v,'s)idl_input \<Rightarrow> bool" where
  "idl_solvable = (\<lambda> (bnds, diffs). (\<exists>\<alpha> :: 'v \<times> 's \<Rightarrow> int.
    (\<forall> (v,b) \<in> set bnds. 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b) \<and>
    (\<forall> c \<in> set diffs. \<exists> (v,w) \<in> set c. \<alpha> v \<noteq> \<alpha> w)))" 

lemma idl_smt_solver_alt_def: "idl_smt_solver solver = (\<forall> bnds diffs.
     idl_input (bnds,diffs) \<longrightarrow> solver bnds diffs = idl_solvable (bnds,diffs))" 
  unfolding idl_smt_solver_def idl_input_def idl_solvable_def by auto
 
text \<open>Delete all variables with (a sort that has) an upper bound of 0;
  if some the clauses becomes empty, return a trivial unsat-problem.\<close>
definition delete_trivial_sorts :: "('v,'s)idl_input \<Rightarrow> ('v,'s)idl_input option" where
  "delete_trivial_sorts = (\<lambda> (bnds, diffs). 
      case partition ((=) 0 o snd) bnds of
       ([],_) \<Rightarrow> Some (bnds, diffs)
     | (triv,non_triv) \<Rightarrow> let triv_sorts = set (map (snd o fst) triv);
            newdiffs = map (filter (\<lambda> vw. snd (fst vw) \<notin> triv_sorts)) diffs
         in if [] \<in> set newdiffs then None else Some (non_triv, newdiffs))" 

lemma delete_trivial_sorts: assumes inp: "idl_input input"
  and del: "delete_trivial_sorts input = ooutput" 
shows "(ooutput = None \<longrightarrow> \<not> idl_solvable input) \<and> (ooutput = Some output \<longrightarrow> idl_input output \<and> idl_solvable input = idl_solvable output)" 
proof -
  obtain bnds diffs where input: "input = (bnds,diffs)" by force
  obtain triv non_triv where part: "partition ((=) 0 o snd) bnds = (triv,non_triv)" (is "partition ?f _ = _") by force
  define f where "f = ?f" 
  note del = del[unfolded delete_trivial_sorts_def input split part]
  show ?thesis
  proof (cases triv)
    case Nil
    thus ?thesis using inp del input by auto
  next
    case Cons
    from part[unfolded partition_filter_conv, folded f_def]
    have triv: "triv = filter f bnds" and non_triv: "non_triv = filter (Not \<circ> f) bnds" by auto
    define tsorts where "tsorts = set (map (snd \<circ> fst) triv)" 
    define newdiffs where "newdiffs = map (filter (\<lambda>vs. snd (fst vs) \<notin> tsorts)) diffs" 
    let ?out = "(non_triv, newdiffs)" 
    note inp = inp[unfolded input idl_input_def split]
    from inp have dist: "distinct (map fst bnds)" by blast
    have out_conds: "idl_input ?out" 
      unfolding idl_input_def split
    proof (intro conjI allI impI)
      show "distinct (map fst non_triv)" unfolding non_triv by (rule distinct_map_filter[OF dist])
      {
        fix v w
        assume "(v, w) \<in> set (concat newdiffs)" 
        from this[unfolded newdiffs_def]
        have vw: "(v, w) \<in> set (concat diffs)" and snd: "snd v \<notin> tsorts" by auto
        from vw inp show eq: "v \<noteq> w" by blast
        from vw inp show eq: "snd v = snd w" by blast
        from vw inp have "{v,w} \<subseteq> fst ` set bnds" by blast
        with snd eq have "{v,w} \<subseteq> fst ` set non_triv" unfolding non_triv triv tsorts_def by force
        thus "u \<in> {v, w} \<Longrightarrow> u \<in> fst ` set non_triv" for u by auto
      }
    qed (insert inp, auto simp: non_triv)
    let ?sat1 = "\<lambda> bnds \<alpha>. (\<forall>(v, b)\<in>set bnds. 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b)" 
    let ?sat2 = "\<lambda> diffs \<alpha>. (\<forall>c\<in>set diffs. \<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w)" 
    let ?sat = "\<lambda> bnds diffs \<alpha>. ?sat1 bnds \<alpha> \<and> ?sat2 diffs \<alpha>" 
    have set_bnds: "set bnds = set triv \<union> set non_triv" using part by fastforce
    have main: "idl_solvable input = idl_solvable ?out" unfolding input
    proof
      assume "idl_solvable (non_triv, newdiffs)" 
      from this[unfolded idl_solvable_def split] obtain \<alpha>
        where sat1: "?sat1 non_triv \<alpha>" and sat2: "?sat2 newdiffs \<alpha>" by blast
      define \<beta> where "\<beta> v = (if snd v \<in> tsorts then 0 else \<alpha> v)" for v
      have \<alpha>\<beta>: "?sat2 newdiffs \<alpha> = ?sat2 newdiffs \<beta>" 
      proof (intro ball_cong[OF refl] bex_cong[OF refl], clarsimp)
        fix vsf v1 s1 v2 s2
        assume *: "vsf \<in> set newdiffs" "((v1,s1),(v2,s2)) \<in> set vsf" 
        from *(1)[unfolded newdiffs_def]
        obtain vs where vs: "vs \<in> set diffs" and vsf: "vsf = filter (\<lambda>vs. snd (fst vs) \<notin> tsorts) vs" by auto
        from *(2)[unfolded vsf]
        have vw: "((v1,s1),(v2,s2)) \<in> set vs" and s1: "s1 \<notin> tsorts" by auto
        from inp vw vs have "s1 = s2" by fastforce          
        with s1 show "(\<alpha> (v1,s1) = \<alpha> (v2,s2)) = (\<beta> (v1,s1) = \<beta> (v2,s2))" unfolding \<beta>_def by auto
      qed
      have "?sat1 bnds \<beta>" unfolding set_bnds using sat1
        unfolding \<beta>_def triv non_triv tsorts_def f_def by force
      moreover have "?sat2 diffs \<beta>" using sat2[unfolded \<alpha>\<beta>] unfolding newdiffs_def by auto
      ultimately show "idl_solvable (bnds, diffs)" unfolding idl_solvable_def by auto
    next
      assume "idl_solvable (bnds, diffs)"
      from this[unfolded idl_solvable_def split] obtain \<alpha>
        where sat1: "?sat1 bnds \<alpha>" and sat2: "?sat2 diffs \<alpha>" by blast
      from sat1 have "?sat1 non_triv \<alpha>" unfolding non_triv by auto
      moreover have "?sat2 newdiffs \<alpha>" 
      proof
        fix vsf
        assume "vsf \<in> set newdiffs" 
        from this[unfolded newdiffs_def]
        obtain vs where vs: "vs \<in> set diffs" and vsf: "vsf = filter (\<lambda>vs. snd (fst vs) \<notin> tsorts) vs" by auto
        from sat2[rule_format, OF vs] obtain v w where vw: "(v,w) \<in> set vs" and diff: "\<alpha> v \<noteq> \<alpha> w" by auto
        from vs vw have vw': "(v,w) \<in> set (concat diffs)" by auto
        from inp vw' have vw_sort: "snd v = snd w" by blast
        from inp vw' have vw_bnds: "{v,w} \<subseteq> fst ` set bnds" by blast
        then obtain b bw where "{(v,b),(w,bw)} \<subseteq> set bnds" by auto
        with inp vw_sort have bnds: "{(v,b),(w,b)} \<subseteq> set bnds" by (metis insert_subset)
        with sat1 have "0 \<le> \<alpha> v" "\<alpha> v \<le> b" "0 \<le> \<alpha> w" "\<alpha> w \<le> b" by auto
        with diff have b0: "b \<noteq> 0" by auto
        have "snd v \<notin> tsorts"  
        proof
          assume "snd v \<in> tsorts" 
          from this[unfolded tsorts_def triv f_def]
          obtain u where u0: "(u,0) \<in> set bnds" and same_sort: "snd u = snd v" by auto
          from bnds inp u0 same_sort have "b = 0" by blast
          with b0 show False by auto
        qed
        with vw have "(v,w) \<in> set vsf" unfolding vsf by auto
        with diff show "\<exists>(v, w)\<in>set vsf. \<alpha> v \<noteq> \<alpha> w" by auto
      qed
      ultimately show "idl_solvable (non_triv, newdiffs)" 
        by (auto simp: idl_solvable_def)
    qed
    have outp: "ooutput = (if [] \<in> set newdiffs then None else Some ?out)" 
      using del by (auto simp: Cons tsorts_def newdiffs_def Let_def)
    show ?thesis
    proof (cases "[] \<in> set newdiffs")
      case False
      thus ?thesis using outp main out_conds by auto
    next
      case True
      from split_list[OF this]
      show ?thesis using outp unfolding main 
        by (auto simp: idl_input_def idl_solvable_def)
    qed
  qed
qed

fun assign_by_sort :: "('s, (int \<times> ('v,int)alist)) mapping \<Rightarrow> (('v \<times> 's) \<times> int) list
  \<Rightarrow> ('s, int \<times> ('v, int)alist) mapping" where
  "assign_by_sort m [] = m" 
| "assign_by_sort m (((v,s),b) # bnds) = (case Mapping.lookup m s of
     None \<Rightarrow> assign_by_sort (Mapping.update s (b,[(v,b)]) m) bnds
   | Some (b,vs) \<Rightarrow> assign_by_sort (Mapping.update s (b - 1, (v, b - 1) # vs) m) bnds)" 

lemma assign_by_sort_computation: fixes bnds :: "(('v \<times> 's) \<times> int) list" and s :: 's
  assumes filt: "filt = filter ((=) s \<circ> snd \<circ> fst) bnds" 
  shows "Mapping.lookup (assign_by_sort Mapping.empty bnds) s = (if filt = [] then None
     else Some
   (snd (hd filt) - int (length filt) + 1,
    rev (map (\<lambda>i. (fst (fst (filt ! i)), snd (hd filt) - int i)) [0..<length filt])))" 
proof -
  let ?f = "\<lambda> m ((v :: 'v,s :: 's),b :: int). case m of None \<Rightarrow> Some (b :: int,[(v,b)]) | Some (b :: int,vs) \<Rightarrow> Some (b - 1, (v, b - 1) # vs)" 
  let ?filt = filt
  define f where "f = ?f" 
  define fi :: "(('v \<times> 's) \<times> int) \<Rightarrow> bool" where "fi = (((=) s) o snd o fst)" 
  {  
    fix a bnds' m
    have "Mapping.lookup m s = foldl f a (filter fi bnds')
    \<Longrightarrow> Mapping.lookup (assign_by_sort m bnds) s = 
    foldl f a (filter fi (bnds' @ bnds))" 
    proof (induct bnds arbitrary: m bnds')
      case (Cons entry bnds m bnds')
      obtain v s' b where entry: "entry = ((v,s'),b)" by (cases entry) auto
      show ?case 
      proof (cases "s' = s")
        case False
        then obtain m' where 
          id: "assign_by_sort m (entry # bnds) = assign_by_sort m' bnds" and m': "Mapping.lookup m' s = Mapping.lookup m s" 
          unfolding entry by (cases "Mapping.lookup m s'", auto)
        from False have False: "\<not> fi entry" unfolding fi_def entry by auto
        show ?thesis unfolding id 
          by (subst Cons(1), rule Cons(2)[folded m'], insert False, auto simp: entry) 
      next
        case True
        obtain m' where
          id: "assign_by_sort m (entry # bnds) = assign_by_sort m' bnds" 
          and m': "Mapping.lookup m' s = f (Mapping.lookup m s) entry" 
          unfolding entry True by (cases "Mapping.lookup m s", auto simp: f_def)
        from True have fi: "fi entry" unfolding entry fi_def by auto
        have filt: "filter fi ((entry # bnds) @ bnds') = entry # filter fi (bnds @ bnds')" 
          unfolding entry True fi_def by auto
        show ?thesis unfolding id filt
          by (subst Cons(1)[where bnds' = "bnds' @ [entry]"], subst m'[unfolded Cons(2)], insert fi, auto)
      qed
    qed auto
  }
  from this[of Mapping.empty None Nil]
  have impl: "Mapping.lookup (assign_by_sort Mapping.empty bnds) s = foldl f None (filter fi bnds)" 
    by auto
  define filt where "filt = filter fi bnds"   
  {
    assume "filt \<noteq> []" 
    then obtain x0 b0 s' bnds'
      where filt: "filt = ((x0,s'),b0) # bnds'" by (cases filt, auto)
    have fold: "foldl f (Some (b,xs)) bnds' = 
       Some (b - int (length bnds'), 
       rev (map2 (\<lambda>i v. (fst (fst v), b - i)) [1.. int (length bnds')] bnds') @ xs)" 
      for b xs
    proof (induct bnds' arbitrary: b xs)
      case (Cons entry bnds)
      obtain x s b' where entry: "entry = ((x,s),b')" by (cases entry) auto  
      have f_entry: "f (Some (b, xs)) entry = Some (b - 1, (x, b - 1) # xs)" 
        unfolding f_def entry by simp
      have list: "[1..int (length bnds + Suc 0)] = 1 # map ((+) 1) [1..int (length bnds)]"
        apply (intro nth_equalityI, force)
        subgoal for i by (cases i, auto)
        done
      have map_eq: "map2 (\<lambda>x y. (fst (fst y), b - 1 - x)) [1..int (length bnds)] bnds =
        map2 (\<lambda>x y. (fst (fst y), b - x)) (map ((+) 1) [1..int (length bnds)]) bnds" 
        by (intro nth_equalityI, auto)
      show ?case unfolding foldl.simps list.size f_entry
        unfolding Cons option.simps prod.simps unfolding list
        by (intro conjI, force, insert map_eq, simp add: entry) 
    qed auto
    have "Mapping.lookup (assign_by_sort Mapping.empty bnds) s = foldl f (Some (b0,[(x0,b0)])) bnds'" 
      unfolding impl filt_def[symmetric] filt by (simp add: f_def)
    also have "\<dots> = Some
     (b0 - int (length filt) + 1,
      rev (map (\<lambda> i. (fst (fst (filt ! i)), b0 - int i)) [0 ..< length filt]))" 
      unfolding fold option.simps prod.simps rev.simps(2)[symmetric]
    proof (intro conjI arg_cong[of _ _ rev])
      show "(x0, b0) # map2 (\<lambda>x y. (fst (fst y), b0 - x)) [1..int (length bnds')] bnds' =
        map (\<lambda>i. (fst (fst (filt ! i)), b0 - int i)) [0..<length filt]" 
        unfolding filt fst_conv list.size
        apply (intro nth_equalityI, force)
        subgoal for i apply (cases i, simp_all add: nth_append)
          by (metis Suc_lessI nth_Cons_Suc)
        done
    qed (simp add: filt)
    finally have "Mapping.lookup (assign_by_sort Mapping.empty bnds) s =
      Some (snd (hd filt) - int (length filt) + 1, rev (map (\<lambda>i. (fst (fst (filt ! i)), snd (hd filt) - int i)) [0..<length filt]))" 
      unfolding filt
      by auto
  } note ne_impl = this
  have filt: "filt = ?filt" unfolding filt filt_def fi_def ..
  show ?thesis
  proof (cases "filt = []")
    case False
    thus ?thesis unfolding ne_impl[OF False] filt by auto
  next
    case True 
    thus ?thesis  using filt unfolding impl filt_def[symmetric] by auto
  qed
qed

definition find_large_sorts :: "(('v \<times> 's) \<times> int) list \<Rightarrow> 's set" where
  "find_large_sorts bnds = (let
      m = assign_by_sort Mapping.empty bnds;
      mf = Mapping.filter (\<lambda> s (b,vs). b \<ge> 0) m
    in Mapping.keys mf)" 

text \<open>Delete all variables of a sort where the upper bound is large
  enough to make all variables of this sort distinct.
  Afterwards also delete all non-occurring variables from the bounds-list.\<close>
definition delete_large_sorts_single :: "('v,'s)idl_input \<Rightarrow> ('v,'s)idl_input \<times> bool" where
  "delete_large_sorts_single = (\<lambda> (bnds, diffs). 
     let lsorts = find_large_sorts bnds 
     in if Set.is_empty lsorts then ((bnds,diffs), False)
      else let newdiffs = filter (\<lambda> vs. \<forall> vw \<in> set vs. snd (fst vw) \<notin> lsorts) diffs;
               remvars = set (List.maps (List.maps (\<lambda> (v,w). [v,w])) newdiffs);
               newbnds = filter (\<lambda> vb. fst vb \<in> remvars) bnds
         in ((newbnds, newdiffs),True))" 


lemma delete_large_sorts_single: assumes inp: "idl_input (input :: ('v,'s)idl_input)"
  and del: "delete_large_sorts_single input = (output,changed)" 
shows "idl_input output \<and> 
   (idl_solvable input = idl_solvable output) \<and> 
   (changed \<longrightarrow> length (fst input) > length (fst output))" 
proof -
  obtain bnds diffs where input: "input = (bnds,diffs)" by force
  define lsorts where "lsorts = find_large_sorts bnds" 
  show ?thesis
  proof (cases "Set.is_empty lsorts")
    case True
    with del inp show ?thesis 
      unfolding delete_large_sorts_single_def input split lsorts_def Let_def by auto
  next
    case False
    define f where "f vs = (\<forall>vw\<in>set vs. snd (fst vw) \<notin> lsorts)" for vs :: "(('v \<times> 's) \<times> 'v \<times> 's) list" 
    define newdiffs where "newdiffs = filter f diffs" 
    define remvars where "remvars = set (List.maps (List.maps (\<lambda>(v, w). [v, w])) newdiffs)" 
    define newbnds where "newbnds = filter (\<lambda>vb. fst vb \<in> remvars) bnds" 
    let ?out = "(newbnds, newdiffs)" 
    from del[unfolded delete_large_sorts_single_def input split] False
    have outp: "output = ?out" 
      by (simp add: Let_def lsorts_def newdiffs_def remvars_def newbnds_def f_def[abs_def])
    note inp = inp[unfolded input idl_input_def split]
    from inp have dist: "distinct (map fst bnds)" by blast
    have nd_sub: "set newdiffs \<subseteq> set diffs" unfolding newdiffs_def by auto
    have nb_sub: "set newbnds \<subseteq> set bnds" unfolding newbnds_def by auto
    have idl_out': "idl_input output" 
      unfolding idl_input_def split outp
    proof (intro conjI allI impI)
      show "distinct (map fst newbnds)" unfolding newbnds_def by (rule distinct_map_filter[OF dist])
      show "\<And>v w b1 b2. (v, b1) \<in> set newbnds \<Longrightarrow> (w, b2) \<in> set newbnds \<Longrightarrow> snd v = snd w \<Longrightarrow> b1 = b2" 
        using nb_sub inp by blast
      show "\<And>v b. (v, b) \<in> set newbnds \<Longrightarrow> 0 \<le> b" using nb_sub inp by blast
      from nd_sub have csub: "set (concat newdiffs) \<subseteq> set (concat diffs)" by auto
      from csub show "\<And>v w. (v, w) \<in> set (concat newdiffs) \<Longrightarrow> snd v = snd w" using inp by (meson in_mono)
      from csub show "\<And>v w. (v, w) \<in> set (concat newdiffs) \<Longrightarrow> v \<noteq> w" using inp by auto
      fix v w u 
      assume vw: "(v, w) \<in> set (concat newdiffs)" and u: "u \<in> {v, w}"
      with csub inp have ubnds: "u \<in> fst ` set bnds" by (meson in_mono)
      from vw u have "u \<in> remvars" unfolding remvars_def List.maps_def 
        by (cases v; cases w; cases u; force)
      with vw u ubnds show "u \<in> fst ` set newbnds" unfolding newbnds_def by force
    qed
    note idl_out = idl_out'[unfolded outp idl_input_def split]
    show ?thesis
    proof (intro conjI impI idl_out')
      let ?sat1 = "\<lambda> bnds \<alpha>. (\<forall>(v, b)\<in>set bnds. 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b)" 
      let ?sat2 = "\<lambda> diffs \<alpha>. (\<forall>c\<in>set diffs. \<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w)" 
      let ?sat = "\<lambda> bnds diffs \<alpha>. ?sat1 bnds \<alpha> \<and> ?sat2 diffs \<alpha>" 
      show "idl_solvable input = idl_solvable output" 
      proof
        (* the trivial direction *)
        assume "idl_solvable input" 
        then obtain \<alpha> where "?sat bnds diffs \<alpha>" unfolding idl_solvable_def input by auto
        hence "?sat newbnds newdiffs \<alpha>" using nd_sub nb_sub by auto
        thus "idl_solvable output" unfolding idl_solvable_def outp by auto
      next
        (* the main property that shows that variables of large sorts can be deleted *)
        assume "idl_solvable output" 
        from this[unfolded idl_solvable_def outp] obtain \<alpha> where
          sat1: "?sat1 newbnds \<alpha>" and sat2: "?sat2 newdiffs \<alpha>" by auto
        define m where "m = assign_by_sort Mapping.empty bnds" 
        define filt where "filt s = filter ((=) s \<circ> snd \<circ> fst) bnds" for s
        define mf where "mf = Mapping.filter (\<lambda> s (b,vs). b \<ge> 0) m" 
        {
          fix s i vs
          assume "Mapping.lookup mf s = Some (i,vs)" 
          from this[unfolded mf_def] have look_m: "Mapping.lookup m s = Some (i,vs)" and i0: "i \<ge> 0" 
            by (transfer, auto split: option.splits if_splits)+
          from look_m[unfolded m_def assign_by_sort_computation[OF filt_def]]
          have i: "i = snd (hd (filt s)) - int (length (filt s)) + 1" 
            and vs: "vs = rev (map (\<lambda>i. (fst (fst (filt s ! i)), snd (hd (filt s)) - int i)) [0..<length (filt s)])" 
            and ne: "filt s \<noteq> []" by (auto split: if_splits)
          from ne obtain x b s' fs where "filt s = ((x,s'),b) # fs"
            by (cases "filt s", auto)
          with arg_cong[OF this, of set, unfolded filt_def] 
          have filt: "filt s = ((x,s),b) # fs" unfolding filt_def by (force simp: o_def)
          from arg_cong[OF filt[unfolded filt_def], of set] 
          have in_bnds: "((x,s),b) \<in> set bnds" by auto
          from filt have hd: "hd (filt s) = ((x,s),b)" by auto
          note i = i[unfolded hd snd_conv]
          note vs = vs[unfolded hd snd_conv]
          from i0[unfolded i]
          have bnd: "int (length (filt s)) \<le> b + 1" by simp
          from arg_cong[OF vs, of "\<lambda> s. snd ` set s"]
          have "snd ` set vs = {b - int j |. j \<in> {0..<length (filt s)}}" by force
          with bnd have bounded: "snd ` set vs \<subseteq> {0..b}" by auto
          have dist: "distinct (map snd vs)" 
            unfolding vs rev_map[symmetric] distinct_rev
            unfolding map_map o_def snd_conv
            unfolding distinct_map by (auto simp: inj_on_def)
          have image: "(fst o fst) ` set (filt s) \<subseteq> fst ` set vs" 
            unfolding vs set_map set_rev fst_conv image_comp o_def set_upt
            unfolding set_conv_nth by auto
          have "\<exists> x b. ((x,s),b) \<in> set bnds \<and> snd ` set vs \<subseteq> {0..b}" using bounded in_bnds by auto
          note image dist this
        } note mf_lookup = this

        (* update the values for variables of large sorts from the assign-by-sort map *)
        define \<beta> where "\<beta> = (\<lambda> (v,s). 
           case Mapping.lookup mf s of None \<Rightarrow> if (v,s) \<in> fst ` set newbnds then \<alpha> (v,s) else 0 | Some (_,vs) \<Rightarrow> the (map_of vs v))" 
        have lsorts: "lsorts = Mapping.keys mf" unfolding mf_def m_def lsorts_def find_large_sorts_def Let_def ..
        have "?sat1 bnds \<beta>" 
        proof (intro ballI, clarsimp)
          fix v s b 
          assume vsb: "((v,s),b) \<in> set bnds" 
          with inp have b0: "b \<ge> 0" by auto
          show "0 \<le> \<beta> (v, s) \<and> \<beta> (v, s) \<le> b" 
          proof (cases "s \<in> lsorts")
            case False  
            hence \<beta>\<alpha>: "\<beta> (v,s) = (if (v,s) \<in> fst ` set newbnds then \<alpha> (v,s) else 0)"  
              unfolding \<beta>_def split lsorts keys_dom_lookup by (cases "Mapping.lookup mf s", auto)
            show ?thesis
            proof (cases "(v,s) \<in> fst ` set newbnds")
              case True
              with vsb have mem: "((v,s),b) \<in> set newbnds" unfolding newbnds_def by auto
              with \<beta>\<alpha> have "\<beta> (v,s) = \<alpha> (v,s)" by force
              from sat1[rule_format, OF mem] this show ?thesis by auto
            next
              case False
              with \<beta>\<alpha> b0 show ?thesis by auto
            qed
          next
            case True
            from this[unfolded lsorts keys_dom_lookup] 
            obtain i vs where look_mf: "Mapping.lookup mf s = Some (i,vs)" by auto
            from vsb have "v \<in> (fst \<circ> fst) ` set (filt s)" unfolding filt_def by force
            with mf_lookup[OF look_mf] obtain x b' where v: "v \<in> fst ` set vs" 
              and x: "((x, s), b') \<in> set bnds" and vs: "snd ` set vs \<subseteq> {0..b'}" by blast
            from x vsb inp have "b' = b" by auto
            note vs = vs[unfolded this]
            from v have "map_of vs v \<noteq> None"
              by (simp add: map_of_eq_None_iff) 
            then obtain i where map: "map_of vs v = Some i" by blast
            from map_of_SomeD[OF this] vs have i: "i \<in> {0..b}" by auto
            have \<beta>: "\<beta> (v,s) = the (map_of vs v)" unfolding \<beta>_def look_mf split by auto
            thus ?thesis unfolding map using i by auto
          qed
        qed
        moreover 
        have "?sat2 diffs \<beta>" 
        proof
          fix c
          assume c: "c \<in> set diffs" 
          show "\<exists>(v, w)\<in>set c. \<beta> v \<noteq> \<beta> w" 
          proof (cases "c \<in> set newdiffs")
            case True
            from this[unfolded newdiffs_def] have fc: "f c" by auto
            from True sat2 obtain v w where vw: "(v,w) \<in> set c" and diff: "\<alpha> v \<noteq> \<alpha> w" by auto
            from fc[unfolded f_def] vw have sort: "snd v \<notin> lsorts" by auto
            from idl_out True vw have vw_bnds: "{v,w} \<subseteq> fst ` set newbnds" unfolding set_concat 
              by (smt (verit, ccfv_SIG) UnionI image_iff subset_eq)
            from idl_out True vw have same_sort: "snd v = snd w" unfolding set_concat by blast
            {
              fix u
              assume "u \<in> {v,w}"
              with sort same_sort vw_bnds obtain x s where
                u: "u = (x,s)" and s: "s \<notin> lsorts" "(x,s) \<in> fst ` set newbnds" by force
              have "\<beta> u = \<alpha> u" unfolding \<beta>_def u split using s 
                by (cases "Mapping.lookup mf s", auto simp: lsorts keys_dom_lookup)
            }
            with vw diff show "\<exists>(v, w)\<in>set c. \<beta> v \<noteq> \<beta> w" 
              by (intro bexI[of _ "(v,w)"], auto)
          next
            case False
            from this[unfolded newdiffs_def] c have "\<not> f c" by auto
            from this[unfolded f_def] obtain v w where 
              vw: "(v,w) \<in> set c" and sort: "snd v \<in> lsorts" by force
            from vw inp c have "snd v = snd w" unfolding set_concat by blast
            with sort obtain x y s where v: "v = (x,s)" and w: "w = (y,s)" and s: "s \<in> lsorts" 
              by (cases v; cases w; auto)
            from s[unfolded lsorts keys_dom_lookup] 
            obtain i vs where look_mf: "Mapping.lookup mf s = Some (i,vs)" by auto
            from vw inp c have "v \<noteq> w" unfolding set_concat by blast
            with v w have xy: "x \<noteq> y" by auto
            have \<beta>v: "\<beta> v = the (map_of vs x)" unfolding \<beta>_def look_mf split v by auto
            have \<beta>w: "\<beta> w = the (map_of vs y)" unfolding \<beta>_def look_mf split w by auto
            show "\<exists>(v, w)\<in>set c. \<beta> v \<noteq> \<beta> w" 
            proof (intro bexI[OF _ vw], unfold split \<beta>v \<beta>w)
              from mf_lookup[OF look_mf] 
              have sub: "(fst \<circ> fst) ` set (filt s) \<subseteq> fst ` set vs" 
                and dist: "distinct (map snd vs)" by auto
              from vw c have "(v,w) \<in> set (concat diffs)" by auto
              with inp have vw: "{v,w} \<subseteq> fst ` set bnds" by blast
              {
                fix z
                assume "z \<in> {x,y}" 
                hence "(z,s) \<in> fst ` set bnds" using vw unfolding v w  by auto
                hence "z \<in> (fst \<circ> fst) ` set (filt s)" unfolding filt_def by force
                with sub have "z \<in> fst ` set vs" by auto
                hence "map_of vs z \<noteq> None" by (simp add: map_of_eq_None_iff)
              }
              from this[of x] this[of y] obtain i j where 
                map: "map_of vs x = Some i" "map_of vs y = Some j" 
                by auto
              hence mem: "(x,i) \<in> set vs" "(y,j) \<in> set vs" by (auto simp: map_of_SomeD)
              then obtain k l where *: "k < length vs" "vs ! k = (x,i)" "l < length vs" "vs ! l = (y,j)" 
                unfolding set_conv_nth by auto
              from * xy have "k \<noteq> l" by auto
              with dist * have ij: "i \<noteq> j" unfolding distinct_conv_nth by force
              thus "the (map_of vs x) \<noteq> the (map_of vs y)" unfolding map by auto
            qed
          qed
        qed
        ultimately show "idl_solvable input" unfolding input idl_solvable_def by auto
      qed
    next
      define m where "m = assign_by_sort Mapping.empty bnds" 
      define filt where "filt s = filter ((=) s \<circ> snd \<circ> fst) bnds" for s
      define mf where "mf = Mapping.filter (\<lambda> s (b,vs). b \<ge> 0) m" 
      from False obtain s where sl: "s \<in> lsorts" by (auto simp: Set.is_empty_def)
      from this[unfolded lsorts_def find_large_sorts_def Let_def, folded m_def]
      have s: "s \<in> Mapping.keys m" using keys_filter by fastforce
      let ?f = "((=) s \<circ> snd \<circ> fst)" 
      from s obtain b vs where "Mapping.lookup m s = Some (b,vs)"
        by (metis in_keysD surj_pair)
      with assign_by_sort_computation[OF filt_def, folded m_def, of s] have "set (filt s) \<noteq> {}" 
        by (auto split: if_splits)
      from this[unfolded filt_def] obtain e where fe: "?f e" and e: "e \<in> set bnds" by auto
      from fe obtain v b where e_id: "e = ((v,s),b)" by (cases e, auto)
      let ?v = "(v,s)" 
      from split_list[OF e] obtain bef aft where bnds: "bnds = bef @ e # aft" by auto
      have e: "fst e \<notin> remvars" 
      proof
        assume "fst e \<in> remvars" 
        from this[unfolded remvars_def e_id fst_conv] obtain w 
          where "(?v,w) \<in> set (concat newdiffs) \<or> (w,?v) \<in> set (concat newdiffs)" 
          unfolding List.maps_def by auto
        from this[unfolded newdiffs_def] obtain vs where f: "f vs" and vs: "vs \<in> set diffs" 
          and "(?v,w) \<in> set vs \<or> (w,?v) \<in> set vs"  by auto
        from this(3) f[unfolded f_def] sl 
        have "(w,?v) \<in> set vs" and snd: "snd w \<noteq> s" by auto
        from this(1) vs have "(w,?v) \<in> set (concat diffs)" by auto
        with inp have "snd w = snd ?v" by blast
        with snd show False by auto
      qed
      have "length (fst output) = length (filter (\<lambda>vb. fst vb \<in> remvars) (bef @ aft))" 
        unfolding outp fst_conv newbnds_def bnds using e by auto
      also have "\<dots> \<le> length (bef @ aft)" by (rule length_filter_le)
      also have "\<dots> < length (fst input)" unfolding input bnds by auto
      finally show "length (fst output) < length (fst input)" .
    qed
  qed
qed

partial_function (tailrec) delete_large_sorts :: "('v,'s)idl_input \<Rightarrow> ('v,'s)idl_input" where
  [code]: "delete_large_sorts inp = (case delete_large_sorts_single inp of
     (out,changed) \<Rightarrow> if changed then delete_large_sorts out else out)" 

lemma delete_large_sorts: assumes "idl_input inp" 
  and del: "delete_large_sorts inp = out" 
shows "idl_input out \<and> idl_solvable inp = idl_solvable out" 
  using assms
proof (induct inp rule: wf_induct[OF wf_measure, of "length o fst"])
  case (1 inp)
  obtain mid ch where single: "delete_large_sorts_single inp = (mid,ch)" (is "?e = _") by (cases ?e, auto)
  from delete_large_sorts_single[OF 1(2) this]
  have *: "idl_input mid" 
    "idl_solvable inp = idl_solvable mid"
    "ch \<Longrightarrow> length (fst mid) < length (fst inp)" 
    by auto
  note out = 1(3)[unfolded delete_large_sorts.simps[of inp, unfolded single split]]
  show ?case
  proof (cases ch)
    case False
    with out * show ?thesis by auto
  next
    case True
    with out have out: "delete_large_sorts mid = out" by auto
    from *(3)[OF True] have "(mid, inp) \<in> measure (length \<circ> fst)" by auto
    from 1(1)[rule_format, OF this *(1) out] * show ?thesis by auto
  qed
qed

definition idl_pre_processor where 
  "idl_pre_processor solver bnds diffs = (case delete_trivial_sorts (bnds, diffs)  
     of None \<Rightarrow> False
     | Some mid \<Rightarrow> let (bnds',diffs') = delete_large_sorts mid
       in if bnds' = [] \<and> diffs' = [] then True else solver bnds' diffs')" 

lemma idl_pre_processor: assumes "idl_smt_solver solver" 
  shows "idl_smt_solver (idl_pre_processor solver)" 
  unfolding idl_smt_solver_alt_def
proof (intro allI impI)
  fix b and d :: "(('a \<times> 'b) \<times> 'a \<times> 'b) list list" 
  assume bd: "idl_input (b, d)" 
  note triv = delete_trivial_sorts[OF bd]
  note res = idl_pre_processor_def[of solver b d]
  show "idl_pre_processor solver b d = idl_solvable (b, d)" 
  proof (cases "delete_trivial_sorts (b,d)")
    case None
    with triv res show ?thesis by auto
  next
    case (Some mid)
    from triv[OF Some, of mid]
    have mid: "idl_input mid" and bd: "idl_solvable (b, d) = idl_solvable mid" by auto
    note res = res[unfolded Some option.simps]  
    obtain ob od where large: "delete_large_sorts mid = (ob,od)" by force
    note res = res[unfolded large Let_def split]
    from delete_large_sorts[OF mid large]
    have out: "idl_input (ob, od)" and mid: "idl_solvable mid = idl_solvable (ob, od)" by auto
    show ?thesis
    proof (cases "ob = [] \<and> od = []")
      case True 
      hence "idl_solvable (ob,od)" unfolding idl_solvable_def by auto
      with True res show ?thesis unfolding bd mid by auto
    next
      case False
      from assms[unfolded idl_smt_solver_alt_def, rule_format, OF out]
      show ?thesis using False unfolding bd mid res by auto
    qed
  qed
qed

datatype 'v idl_constraint = Var_Int (idlc_vi: "'v \<times> int") | Var_Var (idlc_vv : "'v \<times> 'v")

fun is_idlc_vi where
  "is_idlc_vi (Var_Int _) = True" 
| "is_idlc_vi _ = False" 

fun idlc_sat :: "('v \<Rightarrow> int) \<Rightarrow> 'v idl_constraint \<Rightarrow> bool" where
  "idlc_sat \<alpha> (Var_Int (v,i)) = (\<alpha> v \<noteq> i)" 
| "idlc_sat \<alpha> (Var_Var (v,w)) = (\<alpha> v \<noteq> \<alpha> w)" 

fun idlc_vars :: "'v idl_constraint \<Rightarrow> 'v list" where
  "idlc_vars (Var_Int (v,i)) = [v]" 
| "idlc_vars (Var_Var (v,w)) = [v,w]" 

lemma idlc_vi[simp]: "is_idlc_vi vi \<Longrightarrow> Var_Int (idlc_vi vi) = vi" 
  by (cases vi, auto)

lemma idlc_vv[simp]: "\<not> is_idlc_vi vv \<Longrightarrow> Var_Var (idlc_vv vv) = vv" 
  by (cases vv, auto)

datatype 'v idl_constraints = IDL_CS 
    "('v \<times> int)list" 
    "('v \<times> 'v)list" 
    "'v idl_constraint list list"

definition "singleton x = [x]" 

fun is_singleton_list :: "'a list \<Rightarrow> bool" where
  "is_singleton_list [x] = True" 
| "is_singleton_list (x # y # xs) = (x = y \<and> is_singleton_list (x # xs))"
| "is_singleton_list _ = False"

lemma is_singleton_list: "is_singleton_list xs \<Longrightarrow> set (singleton (hd xs)) = set xs" 
  by (induct xs rule: is_singleton_list.induct, auto simp: singleton_def)

fun idl_flat_cs :: "'v idl_constraints \<Rightarrow> 'v idl_constraint set set" where
  "idl_flat_cs (IDL_CS vis vws cs) = set (map set (map (singleton o Var_Int) vis @ map (singleton o Var_Var) vws @ cs))" 

fun idl_cs_restructure :: "'v idl_constraints \<Rightarrow> 'v idl_constraints option" where
  "idl_cs_restructure (IDL_CS vis vws cs) = (if [] \<in> set cs then None else Some (
      case partition is_singleton_list cs of 
       (ss, other) \<Rightarrow> (case partition is_idlc_vi (map hd ss) 
         of (xis,xys) \<Rightarrow> (IDL_CS (map idlc_vi xis @ vis) (map idlc_vv xys @ vws) other))))" 
        

definition idl_flat_vs :: "'v idl_constraints \<Rightarrow> 'v set" where
  "idl_flat_vs C = (\<Union> c \<in> idl_flat_cs C. (\<Union> a \<in> c. set (idlc_vars a)))"  

definition idl_constraints_sat :: "'v idl_constraints \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> bool" where
  "idl_constraints_sat cs \<alpha>  = (\<forall> disj \<in> idl_flat_cs cs. Bex disj (idlc_sat \<alpha>))" 

lemma idl_cs_restructure: assumes "idl_cs_restructure cs = cso" 
  shows "cso = None \<Longrightarrow> \<not> (Ex (idl_constraints_sat cs))" 
    "cso = Some cs' \<Longrightarrow> idl_flat_cs cs = idl_flat_cs cs'" 
    "cso = Some cs' \<Longrightarrow> idl_constraints_sat cs = idl_constraints_sat cs'" 
    "cso = Some cs' \<Longrightarrow> idl_flat_vs cs = idl_flat_vs cs'" 
proof -
  obtain vis vws css where cs: "cs = IDL_CS vis vws css" by (cases cs, auto)
  {
    assume "cso = None" 
    with assms[unfolded cs, simplified] have "[] \<in> set css" by (auto split: if_splits)
    thus "\<not> (Ex (idl_constraints_sat cs))" unfolding cs by (auto simp: idl_constraints_sat_def)
  }  
  obtain ss other where p1: "partition is_singleton_list css = (ss,other)" by force
  obtain xis xys where p2: "partition is_idlc_vi (map hd ss) = (xis,xys)" by force
  have css: "set css = set ss \<union> set other" using p1 by auto
  have id: "map set ss = map (set o singleton) (map hd ss)" unfolding map_map
  proof (rule map_cong[OF refl])
    fix s
    assume "s \<in> set ss" with p1 have "is_singleton_list s" by auto
    thus "set s = (set o singleton \<circ> hd) s" using is_singleton_list[of s] by auto
  qed
  have ss: "set ` set ss = (set o singleton) ` set (map hd ss)" 
    unfolding image_set unfolding id by auto
  have mss: "set (map hd ss) = set xis \<union> set xys" using p2 by auto
  have vi: "(singleton \<circ> Var_Int) ` idlc_vi ` set xis = singleton ` set xis" 
    unfolding image_comp o_def using p2 by auto
  have vv: "(singleton \<circ> Var_Var) ` idlc_vv ` set xys = singleton ` set xys" 
    unfolding image_comp o_def using p2 by auto
  assume "cso = Some cs'" 
  with assms[unfolded cs idl_cs_restructure.simps p1 split p2]
  have cs': "cs' = IDL_CS (map idlc_vi xis @ vis) (map idlc_vv xys @ vws) other" by (auto split: if_splits)
  show "idl_flat_cs cs = idl_flat_cs cs'" 
    unfolding cs cs' idl_flat_cs.simps map_append set_map set_append css image_Un 
    unfolding ss mss vi vv by auto
  thus "idl_constraints_sat cs = idl_constraints_sat cs'" "idl_flat_vs cs = idl_flat_vs cs'" 
    unfolding idl_constraints_sat_def idl_flat_vs_def by auto
qed
  

datatype 'v idl_solver_state = 
  IDL_State "('v,int list)mapping" "'v idl_constraints" 

fun idl_state_sat :: "'v idl_solver_state \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> bool" where
  "idl_state_sat (IDL_State bnds cs) \<alpha>  = (
     (\<forall> v bnd. Mapping.lookup bnds v = Some bnd \<longrightarrow> \<alpha> v \<in> set bnd)
   \<and> idl_constraints_sat cs \<alpha>)" 

fun idl_state :: "'v idl_solver_state \<Rightarrow> 'v set \<Rightarrow> bool" where
  "idl_state (IDL_State bnds cs) V = (
    Ball (Mapping.entries bnds) (\<lambda> (v,ints). distinct ints \<and> (v \<in> V \<or> ints \<noteq> [])) 
  \<and> idl_flat_vs cs \<subseteq> Mapping.keys bnds
  \<and> finite (Mapping.keys bnds))" 

fun idl_vars :: "'v idl_solver_state \<Rightarrow> 'v set" where 
  "idl_vars (IDL_State bnds cs) = Mapping.keys bnds" 

fun idl_size :: "'v idl_solver_state \<Rightarrow> nat" where
  "idl_size (IDL_State bnds cs) = Mapping.size bnds" 


fun idl_restructure :: "'v idl_solver_state \<Rightarrow> 'v idl_solver_state option" where
  "idl_restructure (IDL_State bnds cs) = map_option (IDL_State bnds) (idl_cs_restructure cs)" 


fun idl_delete_vi :: "'v idl_solver_state \<Rightarrow> 'v idl_solver_state \<times> 'v list" where
 "idl_delete_vi (IDL_State bnds (IDL_CS ((v,i) # vis) vws cs)) = (
     map_prod id (Cons v) (idl_delete_vi (IDL_State (Mapping.map_entry v (remove1 i) bnds) (IDL_CS vis vws cs))))" 
| "idl_delete_vi (IDL_State bnds (IDL_CS [] vws cs)) = (
     (IDL_State bnds (IDL_CS [] vws cs)), [])" 

lemma mapping_size_map_entry[simp]: "Mapping.size (Mapping.map_entry x f m) = Mapping.size m"
  unfolding Mapping.size_def keys_map_entry by auto

lemma idl_delete_vi: assumes "idl_delete_vi C = (C',xs)" "idl_state C V" 
  shows "idl_state C' (V \<union> set xs)" "idl_state_sat C' = idl_state_sat C"  
proof -
  have "idl_state C' (V \<union> set xs) \<and> idl_state_sat C' \<alpha> = idl_state_sat C \<alpha>" for \<alpha>
    using assms
  proof (induct C arbitrary: C' xs V rule: idl_delete_vi.induct)
    case (1 bnds v i vis vws cs C xs' V)
    define bnds' where "bnds' = Mapping.map_entry v (remove1 i) bnds" 
    from 1(2)[unfolded idl_delete_vi.simps bnds'_def[symmetric]]
    obtain xs where rec: "idl_delete_vi (IDL_State bnds' (IDL_CS vis vws cs)) = (C,xs)" (is "?e = _")
      and xs': "xs' = v # xs" by (cases ?e, auto)
    have sub: "idl_flat_vs (IDL_CS vis vws cs) \<subseteq> idl_flat_vs (IDL_CS ((v, i) # vis) vws cs)" 
      unfolding idl_flat_vs_def by auto
    have state: "idl_state (IDL_State bnds' (IDL_CS vis vws cs)) (insert v V)" 
      unfolding bnds'_def idl_state.simps keys_map_entry
      unfolding bnds'_def[symmetric]
    proof (intro conjI ballI)
      show "idl_flat_vs (IDL_CS vis vws cs) \<subseteq> Mapping.keys bnds" 
        using 1(3) sub by auto
      fix xb
      assume "xb \<in> Mapping.entries bnds'" 
      then obtain x b where xb: "xb = (x,b)" and look: "Mapping.lookup bnds' x = Some b" 
        by (cases xb, auto dest: in_entriesD)
      note look = look[unfolded lookup_map_entry' bnds'_def]
      then obtain b' where look: "Mapping.lookup bnds x = Some b'" and sub: "b = b' \<or> (x = v \<and> b = remove1 i b')" 
        using set_remove1_subset[of i]
        by (cases "Mapping.lookup bnds x"; cases "v = x", auto)
      from look have "(x,b') \<in> Mapping.entries bnds" by (rule in_entriesI)
      with 1(3)[simplified] have "distinct b'" and V: "(x \<in> V \<or> b' \<noteq> [])" by auto
      with sub have "distinct b" by auto
      with V sub show "case xb of (x, b) \<Rightarrow> distinct b \<and> (x \<in> insert v V \<or> b \<noteq> [])" 
        unfolding xb by auto
    qed (insert 1(3), auto)
    
    note IH = 1(1)[OF rec[unfolded bnds'_def], folded bnds'_def, OF state]

    have "idl_state_sat (IDL_State bnds (IDL_CS ((v, i) # vis) vws cs)) \<alpha>
      = ((\<alpha> v \<noteq> i \<and> (\<forall> v ints. Mapping.lookup bnds v = Some ints \<longrightarrow> \<alpha> v \<in> set ints)) 
        \<and> idl_constraints_sat (IDL_CS vis vws cs) \<alpha>)" 
      unfolding idl_state_sat.simps
      by (auto simp add: idl_constraints_sat_def singleton_def)
    also have "(\<alpha> v \<noteq> i \<and> (\<forall> v ints. Mapping.lookup bnds v = Some ints \<longrightarrow> \<alpha> v \<in> set ints))
      = (\<forall> v ints. Mapping.lookup bnds' v = Some ints \<longrightarrow> \<alpha> v \<in> set ints)" (is "?l = ?r")
    proof
      assume ?l
      show ?r
      proof (intro allI conjI impI)
        fix w ints 
        assume "Mapping.lookup bnds' w = Some ints" 
        from this[unfolded lookup_map_entry' bnds'_def]
        show "\<alpha> w \<in> set ints" 
          using \<open>?l\<close>[THEN conjunct2, rule_format, of w] \<open>?l\<close>[THEN conjunct1]
          by (cases "Mapping.lookup bnds w"; cases "v = w", auto)
      qed
    next
      assume ?r
      show ?l
      proof (intro conjI allI impI)
        fix w ints 
        assume "Mapping.lookup bnds w = Some ints" 
        with \<open>?r\<close>[rule_format, of w, unfolded bnds'_def lookup_map_entry']
        show "\<alpha> w \<in> set ints" using set_remove1_subset[of i]
          by (cases "v = w", auto)
      next
        from 1(3) have v: "v \<in> Mapping.keys bnds" by (auto simp: idl_flat_vs_def singleton_def)
        then obtain ints where look: "Mapping.lookup bnds v = Some ints" by (meson in_keysD)
        hence "(v,ints) \<in> Mapping.entries bnds" by (rule in_entriesI)
        with 1(3) have "distinct ints" by auto
        from \<open>?r\<close>[rule_format, of v, unfolded bnds'_def lookup_map_entry, unfolded look]
          set_remove1_eq[OF this]
        show "\<alpha> v \<noteq> i" by auto
      qed
    qed
    also have "(\<dots> \<and> idl_constraints_sat (IDL_CS vis vws cs) \<alpha>) 
      = idl_state_sat (IDL_State bnds' (IDL_CS vis vws cs)) \<alpha>" 
      by (auto simp add: idl_constraints_sat_def singleton_def)
    finally have equiv: "idl_state_sat (IDL_State bnds (IDL_CS ((v, i) # vis) vws cs)) \<alpha> =
      idl_state_sat (IDL_State bnds' (IDL_CS vis vws cs)) \<alpha>" . 
    show ?case unfolding equiv using IH xs' unfolding bnds'_def idl_size.simps by auto
  qed auto
  thus "idl_state C' (V \<union> set xs)" "idl_state_sat C' = idl_state_sat C" by auto
qed

lemma idl_delete_vi_size: "idl_delete_vi C = (C',vs) \<Longrightarrow> idl_size C' \<le> idl_size C" 
proof -
  have "idl_size (fst (idl_delete_vi C)) = idl_size C"
    by (induct C rule: idl_delete_vi.induct, auto)
  thus "idl_delete_vi C = (C',vs) \<Longrightarrow> idl_size C' \<le> idl_size C" by auto
qed
  

lemma idl_restructure: "idl_restructure s = None \<Longrightarrow> \<not> Ex (idl_state_sat s)" 
  "idl_restructure s = Some s' \<Longrightarrow> idl_state_sat s' = idl_state_sat s" 
  "idl_restructure s = Some s' \<Longrightarrow> idl_state s' = idl_state s"
  "idl_restructure s = Some s' \<Longrightarrow> idl_size s' = idl_size s"
proof - 
  obtain bnds cs where s: "s = IDL_State bnds cs" by (cases s, auto)
  note re = idl_cs_restructure[OF refl, of cs]
  note def = idl_restructure.simps[of bnds cs, folded s]
  {
    assume "idl_restructure s = None" 
    with re(1) def show "\<not> Ex (idl_state_sat s)" unfolding s by auto
  }
  assume "idl_restructure s = Some s'" 
  with def obtain cs' where cs: "idl_cs_restructure cs = Some cs'" and s': "s' = IDL_State bnds cs'" 
    by (cases "idl_cs_restructure cs", auto)
  note re = re(2-)[OF cs] 
  from re show "idl_state_sat s' = idl_state_sat s" unfolding s s' by auto
  from re show "idl_state s' = idl_state s" unfolding s' s by auto
  show "idl_size s' = idl_size s" unfolding s' s by simp
qed
  

lemma all_entries_eq_all_lookups:  
  "(\<forall>(x, i)\<in>Mapping.entries m. P x i) = (\<forall>x i. Mapping.lookup m x = Some i \<longrightarrow> P x i)" 
  by (metis case_prodI2 case_prod_conv in_entriesD in_entriesI)

fun inst_vv where "inst_vv v i [] = Some ([],[])" 
  | "inst_vv v i ((x,y) # xs) = (if x = v then (if y = v then None 
       else map_option (map_prod (Cons (y,i)) id) (inst_vv v i xs))
       else if y = v then map_option (map_prod (Cons (x,i)) id) (inst_vv v i xs)
       else map_option (map_prod id (Cons (x,y))) (inst_vv v i xs))" 

lemma inst_vv: assumes "\<alpha> v = i" 
  shows "inst_vv v i vvs = None \<Longrightarrow> \<not> Ball (set (map Var_Var vvs)) (idlc_sat \<alpha>)" 
    "inst_vv v i vvs = Some (vis, nvvs) \<Longrightarrow> Ball (set (map Var_Var vvs)) (idlc_sat \<alpha>)
       = (Ball (set (map Var_Int vis)) (idlc_sat \<alpha>) \<and> Ball (set (map Var_Var nvvs)) (idlc_sat \<alpha>))" 
    "inst_vv v i vvs = Some (vis, nvvs) \<Longrightarrow> set (concat (map (idlc_vars o Var_Int) vis)) \<union> set (concat (map (idlc_vars o Var_Var) nvvs))
       \<subseteq> set (concat (map (idlc_vars o Var_Var) vvs)) - {v}" 
proof (atomize (full), induct vvs arbitrary: vis nvvs)
  case (Cons xy xs fvis fvvs)
  obtain x y where xy: "xy = (x,y)" by force
  show ?case
  proof (cases "x = v \<and> y = v")
    case True
    thus ?thesis by (auto simp: xy)
  next
    case False
    show ?thesis
    proof (cases "inst_vv v i xs")
      case None
      from Cons(1)[THEN conjunct1, rule_format, OF this]
      show ?thesis using None xy by auto
    next
      case (Some pair)
      then obtain nvis nvvs where inst: "inst_vv v i xs = Some (nvis, nvvs)" by (cases pair, auto)
      have simp: "inst_vv v i (xy # xs) = (if x = v then if y = v then None else Some ((y, i) # nvis, nvvs)
         else if y = v then Some ((x, i) # nvis, nvvs) else Some (nvis, (x, y) # nvvs))" 
        unfolding xy inst_vv.simps inst by simp
      note IH = Cons(1)[THEN conjunct2]
      note IH = IH[THEN conjunct1, rule_format, OF inst] IH[THEN conjunct2, rule_format, OF inst]
      from False have nN: "inst_vv v i (xy # xs) \<noteq> None" unfolding simp by auto
      show ?thesis  
      proof (intro conjI impI)
        have "(\<forall>a\<in>set (map Var_Var (xy # xs)). idlc_sat \<alpha> a)
           = (\<alpha> x \<noteq> \<alpha> y \<and> ((\<forall>a\<in>set (map Var_Var xs). idlc_sat \<alpha> a)))" 
          unfolding xy by auto
        note IH_sat = this[unfolded IH(1)]
        assume "inst_vv v i (xy # xs) = Some (fvis, fvvs)" 
        from this[unfolded simp] False
        have eq: "(fvis, fvvs) = (if x = v then ((y, i) # nvis, nvvs)
          else if y = v then ((x, i) # nvis, nvvs) else (nvis, (x, y) # nvvs))" by auto
        show "(\<forall>a\<in>set (map Var_Var (xy # xs)). idlc_sat \<alpha> a) =
         ((\<forall>a\<in>set (map Var_Int fvis). idlc_sat \<alpha> a) \<and> (\<forall>a\<in>set (map Var_Var fvvs). idlc_sat \<alpha> a))" 
          unfolding IH_sat using eq False assms
          by (cases "x = v"; cases "y = v"; auto)
        show "set (concat (map (idlc_vars \<circ> Var_Int) fvis)) \<union> set (concat (map (idlc_vars \<circ> Var_Var) fvvs))
          \<subseteq> set (concat (map (idlc_vars \<circ> Var_Var) (xy # xs))) - {v}" 
          using eq IH(2) False xy
          by (cases "x = v"; cases "y = v"; auto)
      qed (insert nN, auto)
    qed
  qed      
qed auto

fun inst_idlc :: "'v \<Rightarrow> int \<Rightarrow> 'v idl_constraint list \<Rightarrow> 'v idl_constraint list option" where
  "inst_idlc v i [] = Some []" 
| "inst_idlc v i (Var_Var (x,y) # xs) = (if x = v then (if y = v then inst_idlc v i xs else 
      map_option (Cons (Var_Int (y,i))) (inst_idlc v i xs))
     else if y = v then map_option (Cons (Var_Int (x,i))) (inst_idlc v i xs)
     else map_option (Cons (Var_Var (x,y))) (inst_idlc v i xs))" 
| "inst_idlc v i (Var_Int (x,j) # xs) = (if v = x then (if i = j then inst_idlc v i xs else None)
      else map_option (Cons (Var_Int (x,j))) (inst_idlc v i xs))" 

fun inst_idlc_list :: "'v \<Rightarrow> int \<Rightarrow> 'v idl_constraint list list \<Rightarrow> 'v idl_constraint list list" where
  "inst_idlc_list v i [] = []" 
| "inst_idlc_list v i (vs # vvs) = (case inst_idlc v i vs of 
     None \<Rightarrow> inst_idlc_list v i vvs
   | Some vs' \<Rightarrow> vs' # inst_idlc_list v i vvs)" 

lemma inst_idlc: assumes "\<alpha> v = i"
  shows "inst_idlc v i cs = None \<Longrightarrow> Bex (set cs) (idlc_sat \<alpha>)" 
    "inst_idlc v i cs = Some cs' \<Longrightarrow> Bex (set cs') (idlc_sat \<alpha>) = Bex (set cs) (idlc_sat \<alpha>)" 
    "inst_idlc v i cs = Some cs' \<Longrightarrow> set (concat (map idlc_vars cs')) \<subseteq> set (concat (map idlc_vars cs)) - {v}" 
proof (atomize(full), induct cs arbitrary: cs')
  case (Cons a xs)
  note IH_None = Cons[THEN conjunct1, rule_format]
  note IH_Some_sat = Cons[THEN conjunct2, THEN conjunct1, rule_format]
  note IH_Some_vs = Cons[THEN conjunct2, THEN conjunct2, rule_format]
  have bex: "Bex (set (a # xs)) (idlc_sat \<alpha>) = (idlc_sat \<alpha> a \<or> Bex (set xs) (idlc_sat \<alpha>))" by auto  
  show ?case 
  proof (cases a)
    case (Var_Int xj)
    then obtain x j where a: "a = Var_Int (x,j)" by (cases xj, auto)
    show ?thesis
    proof (cases "inst_idlc v i xs")
      case None
      with IH_None[OF this] assms 
      show ?thesis unfolding a bex by auto
    next
      case (Some ys)  
      show ?thesis unfolding bex IH_Some_sat[OF Some, symmetric]
        using IH_Some_vs[OF Some]
        unfolding inst_idlc.simps a Some using assms 
        by (cases "x = v"; cases "i = j"; force)
    qed
  next
    case (Var_Var xy)
    then obtain x y where a: "a = Var_Var (x,y)" by (cases xy, auto)
    show ?thesis
    proof (cases "inst_idlc v i xs")
      case None
      with IH_None[OF this] assms 
      show ?thesis unfolding a bex by auto
    next
      case (Some ys)  
      show ?thesis unfolding bex IH_Some_sat[OF Some, symmetric]
        using IH_Some_vs[OF Some]
        unfolding inst_idlc.simps a Some using assms
        by (cases "x = v"; cases "y = v"; force)
    qed
  qed
qed auto

lemma inst_idlc_list: assumes "\<alpha> v = i"
  shows "Ball (set (inst_idlc_list v i ccs)) (\<lambda> cs. Bex (set cs) (idlc_sat \<alpha>))
     = Ball (set ccs) (\<lambda> cs. Bex (set cs) (idlc_sat \<alpha>))" 
    "set (concat (concat (map (map idlc_vars) (inst_idlc_list v i ccs)))) \<subseteq> set (concat (concat (map (map idlc_vars) ccs))) - {v}"   
proof (atomize(full), induct ccs)
  case (Cons cs ccs)
  note step = inst_idlc[of \<alpha>, OF assms, of cs]
  show ?case 
  proof (cases "inst_idlc v i cs")
    case None
    with step(1)[OF this] Cons show ?thesis by auto
  next
    case (Some cs')
    show ?thesis
    proof (intro conjI)
      show "(\<forall>cs\<in>set (inst_idlc_list v i (cs # ccs)). \<exists>a\<in>set cs. idlc_sat \<alpha> a) =
        (\<forall>cs\<in>set (cs # ccs). \<exists>a\<in>set cs. idlc_sat \<alpha> a)" 
        using step(2)[OF Some] Cons[THEN conjunct1] Some by auto
      show "set (concat (concat (map (map idlc_vars) (inst_idlc_list v i (cs # ccs)))))
        \<subseteq> set (concat (concat (map (map idlc_vars) (cs # ccs)))) - {v}" 
        using step(3)[OF Some] Cons[THEN conjunct2] unfolding inst_idlc_list.simps Some option.simps 
          list.simps concat.simps 
        unfolding set_concat  set_map set_append by fastforce
    qed
  qed
qed auto


fun instantiate_var :: "'v \<Rightarrow> int \<Rightarrow> 'v idl_solver_state \<Rightarrow> 'v idl_solver_state option" where
  "instantiate_var v i (IDL_State bnds (IDL_CS vis vws cs)) = (
     case partition (((=) v) o fst) vis of
       (cvis,nvis1) \<Rightarrow> if i \<in> set (map snd cvis) then None
      else (case inst_vv v i vws of None \<Rightarrow> None
        | Some (nvis2, nvws) \<Rightarrow> let
           ncs = inst_idlc_list v i cs
         in if [] \<in> set ncs then None
         else Some (IDL_State (Mapping.delete v bnds) (IDL_CS (nvis1 @ nvis2) nvws ncs))))" 

lemma lookup_delete_upd: "Mapping.lookup (Mapping.delete x m) = (Mapping.lookup m) (x := None)" 
  apply (intro ext)
  subgoal for y by (cases "x = y", auto)
  done

lemma instantiate_var: assumes "\<alpha> v = i" 
  and "Mapping.lookup bnds v = Some ints" 
  and "i \<in> set ints" 
  and "instantiate_var v i (IDL_State bnds css) = so" 
  and "idl_state (IDL_State bnds css) (insert v V)" 
shows "so = None \<Longrightarrow> \<not> idl_state_sat (IDL_State bnds css) \<alpha>" 
  "so = Some s \<Longrightarrow> idl_state s V \<and> idl_state_sat (IDL_State bnds css) \<alpha> = idl_state_sat s \<alpha>
     \<and> idl_vars s = idl_vars (IDL_State bnds css) - {v}
     \<and> idl_size s < idl_size (IDL_State bnds css)" 
proof (atomize(full), goal_cases)
  case 1
  obtain vis vws cs where css: "css = IDL_CS vis vws cs" by (cases css, auto)
  obtain cvis nvis1 where p1: "partition (((=) v) o fst) vis = (cvis,nvis1)" by force
  let ?res = "instantiate_var v i (IDL_State bnds css)" 
  note res = instantiate_var.simps[of v i bnds vis vws cs, folded css, unfolded p1 split]
  show ?case
  proof (cases "i \<in> set (map snd cvis)")
    case True
    with res have res: "?res = None" by auto
    from True p1 have "(v,i) \<in> set vis" by auto
    from split_list[OF this] assms(1)
    have "\<not> idl_state_sat (IDL_State bnds css) \<alpha>" unfolding css 
      by (auto simp: idl_constraints_sat_def singleton_def)
    with res show ?thesis using assms by auto
  next
    case cvis: False
    hence "(i \<in> set (map snd cvis)) = False" by auto
    note res = res[unfolded this if_False]
    note inst_vv = inst_vv[of \<alpha>, OF assms(1)]
    show ?thesis
    proof (cases "inst_vv v i vws")
      case None
      from inst_vv(1)[OF this] res[unfolded this] assms(4)
      show ?thesis by (auto simp: css idl_constraints_sat_def singleton_def)
    next
      case (Some pairs)
      then obtain nvis2 nvws where ivv: "inst_vv v i vws = Some (nvis2, nvws)" by force
      define ncs where "ncs = inst_idlc_list v i cs" 
      note res = res[unfolded ivv option.simps split Let_def, folded ncs_def]
      note inst_vv = inst_vv(2-3)[OF ivv]
      note inst_cs = inst_idlc_list[of \<alpha> v i cs, folded ncs_def, OF assms(1)]
      show ?thesis
      proof (cases "[] \<in> set ncs")
        case True
        with inst_cs have unsat: "\<not> (\<forall>cs\<in>set cs. Bex (set cs) (idlc_sat \<alpha>))" by auto
        from True res assms(4) have res: "so = None" by auto
        from unsat have "\<not> idl_state_sat (IDL_State bnds css) \<alpha>" 
          unfolding css by (auto simp: idl_constraints_sat_def)
        with res show ?thesis by auto
      next
        case False
        with res assms(4) 
        have so: "so = Some (IDL_State (Mapping.delete v bnds) (IDL_CS (nvis1 @ nvis2) nvws ncs))" 
          (is "_ = Some ?s")
          by auto
        show ?thesis
        proof (intro conjI impI)
          show "so = None \<Longrightarrow> \<not> idl_state_sat (IDL_State bnds css) \<alpha>" using so by auto

          assume "so = Some s"
          with so have s: "s = ?s" by auto
          show "idl_state_sat (IDL_State bnds css) \<alpha> = idl_state_sat s \<alpha>" unfolding s css 
              idl_state_sat.simps
          proof (intro arg_cong2[of _ _ _ _ "(\<and>)"])
            show "(\<forall>v bnd. Mapping.lookup bnds v = Some bnd \<longrightarrow> \<alpha> v \<in> set bnd) =
               (\<forall>x bnd. Mapping.lookup (Mapping.delete v bnds) x = Some bnd \<longrightarrow> \<alpha> x \<in> set bnd)" (is "?l = ?r")
            proof
              show "?l \<Longrightarrow> ?r" by (auto simp: lookup_delete_upd)
              assume ?r
              show ?l
              proof (intro allI impI)
                fix x bnd
                assume "Mapping.lookup bnds x = Some bnd" 
                thus "\<alpha> x \<in> set bnd" using \<open>?r\<close>[rule_format, of x bnd] assms
                  by (cases "x = v", auto simp: lookup_delete_upd)
              qed
            qed
          next
            have "idl_constraints_sat (IDL_CS vis vws cs) \<alpha> = 
               (idl_constraints_sat (IDL_CS vis [] []) \<alpha> \<and>
                idl_constraints_sat (IDL_CS [] vws []) \<alpha> \<and>
                idl_constraints_sat (IDL_CS [] [] cs) \<alpha>)" 
              by (auto simp: idl_constraints_sat_def)
            also have "idl_constraints_sat (IDL_CS vis [] []) \<alpha> = 
                (\<forall>disj\<in>set vis. idlc_sat \<alpha> (Var_Int disj))" 
              unfolding idl_constraints_sat_def by (simp add: singleton_def)
            also have "\<dots> = ((\<forall>disj\<in>set cvis. idlc_sat \<alpha> (Var_Int disj))
                \<and> (\<forall>disj\<in>set nvis1. idlc_sat \<alpha> (Var_Int disj)))" 
              using p1 by auto
            also have "(\<forall>disj\<in>set cvis. idlc_sat \<alpha> (Var_Int disj)) = True" 
              using p1 cvis assms(1) by force
            also have "idl_constraints_sat (IDL_CS [] vws []) \<alpha> = Ball (set (map Var_Var vws)) (idlc_sat \<alpha>)" 
              unfolding idl_constraints_sat_def by (simp add: singleton_def)
            also have "\<dots> = ((Ball (set (map Var_Int nvis2)) (idlc_sat \<alpha>) \<and> Ball (set (map Var_Var nvws)) (idlc_sat \<alpha>)))" unfolding inst_vv ..
            also have "idl_constraints_sat (IDL_CS [] [] cs) \<alpha> = (\<forall>cs\<in>set cs. Bex (set cs) (idlc_sat \<alpha>))" 
              unfolding idl_constraints_sat_def by simp
            also have "\<dots> = (\<forall>cs\<in>set ncs. Bex (set cs) (idlc_sat \<alpha>))" unfolding inst_cs ..
            finally have id: "idl_constraints_sat (IDL_CS vis vws cs) \<alpha> =
               ((\<forall>disj\<in>set (nvis1 @ nvis2). idlc_sat \<alpha> (Var_Int disj)) \<and>
                 (\<forall>a\<in>set (map Var_Var nvws). idlc_sat \<alpha> a) \<and>
                 (\<forall>cs\<in>set ncs. Bex (set cs) (idlc_sat \<alpha>)))" by auto
            show "idl_constraints_sat (IDL_CS vis vws cs) \<alpha> = idl_constraints_sat (IDL_CS (nvis1 @ nvis2) nvws ncs) \<alpha>" 
              unfolding id unfolding idl_constraints_sat_def by (auto simp: singleton_def)
          qed

          note idl = assms(5)[unfolded idl_state.simps]

          show "idl_state s V" unfolding s idl_state.simps
          proof (intro conjI ballI, clarsimp)        
            fix x b
            assume "(x,b) \<in> Mapping.entries (Mapping.delete v bnds)" 
            hence "Mapping.lookup (Mapping.delete v bnds) x = Some b" by (rule in_entriesD)
            from this[unfolded lookup_delete_upd]
            have xv: "x \<noteq> v" and "Mapping.lookup bnds x = Some b" by (cases "x = v", auto)+
            hence "(x,b) \<in> Mapping.entries bnds" by (intro in_entriesI)
            with idl xv show "distinct b \<and> (x \<in> V \<or> b \<noteq> [])" by auto
          next
            let ?VI = "\<lambda> vi. \<Union>x\<in>set vi. set (idlc_vars (Var_Int x))" 
            let ?VV = "\<lambda> vv. (\<Union>x\<in>set vv. set (idlc_vars (Var_Var x)))" 
            let ?CS = "\<lambda> cs. (\<Union>x\<in>set cs. \<Union>a\<in>set x. set (idlc_vars a))" 
            have "idl_flat_vs (IDL_CS (nvis1 @ nvis2) nvws ncs) = 
               ?VI nvis1 \<union> (?VI nvis2 \<union> ?VV nvws) \<union> ?CS ncs" unfolding idl_flat_vs_def 
              by (auto simp: singleton_def)
            also have "\<dots> \<subseteq> (?VI vis - {v}) \<union> (?VV vws - {v}) \<union> (?CS cs - {v})" 
            proof (intro Un_mono)
              show "?VI nvis1 \<subseteq> ?VI vis - {v}" using p1 by auto
              show "?VI nvis2 \<union> ?VV nvws \<subseteq> ?VV vws - {v}" using inst_vv(2) by auto
              show "?CS ncs \<subseteq> ?CS cs - {v}" using inst_cs(2) by auto
            qed
            also have "\<dots> \<subseteq> idl_flat_vs (IDL_CS vis vws cs) - {v}" 
              unfolding idl_flat_vs_def by (auto simp: singleton_def)
            also have "\<dots> \<subseteq> Mapping.keys bnds - {v}"
              using idl[unfolded css] by auto
            also have "\<dots> = Mapping.keys (Mapping.delete v bnds)" by simp
            finally show "idl_flat_vs (IDL_CS (nvis1 @ nvis2) nvws ncs) \<subseteq> Mapping.keys (Mapping.delete v bnds)" 
              by auto
            show "finite (Mapping.keys (Mapping.delete v bnds))" using idl by auto
          qed

          show "idl_vars s = idl_vars (IDL_State bnds css) - {v}" unfolding s idl_vars.simps by auto

          from assms(2) have v: "v \<in> Mapping.keys bnds"
            unfolding keys_is_none_rep by auto
          hence sub: "Mapping.keys (Mapping.delete v bnds) \<subset> Mapping.keys bnds" by auto
          from idl have "finite (Mapping.keys bnds)" by auto
          with sub show "idl_size s < idl_size (IDL_State bnds css)" unfolding s idl_size.simps 
            unfolding Mapping.size_def by (simp add: psubset_card_mono)
        qed
      qed
    qed
  qed
qed

lemma instantiate_var_size: assumes "instantiate_var v i s = Some s'" 
  shows "idl_size s' \<le> idl_size s" 
proof -
  obtain bnds css where s: "s = IDL_State bnds css" by (cases s, auto)  
  obtain vis vws cs where css: "css = IDL_CS vis vws cs" by (cases css, auto)
  note s = s[unfolded css]
  show ?thesis using assms unfolding s by (auto split: if_splits option.splits simp: Let_def size_delete)
qed

fun idl_cs_empty :: "'v idl_solver_state \<Rightarrow> bool" where
  "idl_cs_empty (IDL_State bnds (IDL_CS [] [] [])) = True" 
| "idl_cs_empty _ = False" 

lemma idl_cs_empty: assumes "idl_state s {}" 
  and "idl_cs_empty s" 
shows "Ex (idl_state_sat s)" 
proof -
  obtain bnds where s: "s = IDL_State bnds (IDL_CS [] [] [])" 
    using assms by (cases s rule: idl_cs_empty.cases, auto)
  have "idl_state_sat s (\<lambda> v. hd (the (Mapping.lookup bnds v)))" 
    using assms
    unfolding s by (auto simp: idl_constraints_sat_def all_entries_eq_all_lookups)
  thus ?thesis by blast
qed
  
lemma idl_vars: assumes "\<And> v. v \<in> idl_vars s \<Longrightarrow> \<alpha> v = \<beta> v" 
  and "idl_state s V" 
  shows "idl_state_sat s \<alpha> = idl_state_sat s \<beta>" 
proof -
  obtain bnds c where s: "s = IDL_State bnds c" by (cases s, auto)
  show ?thesis unfolding s idl_state_sat.simps
  proof (intro arg_cong2[of _ _ _ _ "(\<and>)"] all_cong1 imp_cong refl arg_cong[of _ _ "\<lambda> x. x \<in> _"])
    fix v bnd 
    show "Mapping.lookup bnds v = Some bnd \<Longrightarrow> \<alpha> v = \<beta> v" 
      by (intro assms(1), auto simp: s keys_is_none_rep) 
    show "idl_constraints_sat c \<alpha> = idl_constraints_sat c \<beta>" 
      unfolding idl_constraints_sat_def
    proof (intro ball_cong refl bex_cong)
      fix as a
      assume "as \<in> idl_flat_cs c" "a \<in> as" 
      with assms(2)[unfolded s idl_state.simps idl_flat_vs_def]
      have "set (idlc_vars a) \<subseteq> idl_vars s" by (auto simp: s)
      thus "idlc_sat \<alpha> a = idlc_sat \<beta> a" using assms(1) by (cases a, auto)
    qed
  qed
qed
 

fun clean_bnds :: "'v idl_solver_state \<Rightarrow> 'v list \<Rightarrow> 'v idl_solver_state + bool" where
  "clean_bnds s [] = (if idl_cs_empty s then Inr True else Inl s)" 
| "clean_bnds (IDL_State bnds c) (v # vs) = (case Mapping.lookup bnds v of
     None \<Rightarrow> clean_bnds (IDL_State bnds c) vs
   | Some ints \<Rightarrow> (case ints of 
       [] \<Rightarrow> Inr False
     | [i] \<Rightarrow> (case instantiate_var v i (IDL_State bnds c) of None \<Rightarrow> Inr False 
          | Some s \<Rightarrow> clean_bnds s vs)
     | _ \<Rightarrow> clean_bnds (IDL_State bnds c) vs
      ))"

lemma clean_bnds: assumes "idl_state s (set vs)" 
  and "clean_bnds s vs = res" 
shows "res = Inr b \<Longrightarrow> b = (Ex (idl_state_sat s))" 
  "res = Inl s' \<Longrightarrow> idl_state s' {} \<and> Ex (idl_state_sat s') = Ex (idl_state_sat s)" 
proof (atomize(full), insert assms, induct vs arbitrary: s)
  case (Nil s)
  show ?case
  proof (cases "idl_cs_empty s")
    case True
    with idl_cs_empty[of s] Nil show ?thesis by auto
  next
    case False
    thus ?thesis using Nil by auto
  qed
next
  case (Cons v vs s)
  obtain bnds cs where s: "s = IDL_State bnds cs" by (cases s, auto)
  note idl = Cons(2)
  note res = Cons(3)[symmetric, unfolded s clean_bnds.simps]
  show ?case
  proof (cases "Mapping.lookup bnds v")
    case None
    from res[unfolded this]
    have res: "clean_bnds s vs = res" by (auto simp: s)
    from None idl have "idl_state s (set vs)" 
      unfolding s idl_state.simps all_entries_eq_all_lookups by force
    note IH = Cons(1)[OF this res]
    thus ?thesis .
  next
    case (Some ints)
    note res = res[unfolded Some option.simps]
    show ?thesis
    proof (cases ints)
      case Nil
      with res have res: "res = Inr False" by auto
      have "\<not> idl_state_sat s \<alpha>" for \<alpha> unfolding s using Some[unfolded Nil]
        unfolding idl_state_sat.simps all_entries_eq_all_lookups by force
      with res show ?thesis by auto
    next
      case ints: (Cons i nums)
      show ?thesis
      proof (cases "nums = []")
        case True
        with ints have ints: "ints = [i]" by auto
        note res = res[unfolded ints list.simps]
        note Some = Some[unfolded ints]
        have ex: "Ex (idl_state_sat s) = (\<exists> \<alpha>. idl_state_sat s \<alpha> \<and> \<alpha> v = i)" 
          unfolding s idl_state_sat.simps all_entries_eq_all_lookups using Some 
          by (intro ex_cong1, force)        
        show ?thesis
        proof (cases "instantiate_var v i (IDL_State bnds cs)")
          case None
          with res have "res = Inr False" by auto
          moreover have "\<alpha> v = i \<Longrightarrow> \<not> idl_state_sat s \<alpha>" for \<alpha>
            using instantiate_var(1)[OF _ Some _ None, folded s, of \<alpha> "set vs"] idl by auto
          with ex have "\<not> (Ex (idl_state_sat s))" by auto
          ultimately show ?thesis by auto
        next
          case s'': (Some s'')
          with res have res: "clean_bnds s'' vs = res" by auto
          from instantiate_var(2)[OF _ Some _ s'' _ refl, folded s, of _ "set vs"]
          have step: "\<alpha> v = i \<Longrightarrow> idl_state s'' (set vs) \<and> idl_state_sat s \<alpha> = idl_state_sat s'' \<alpha>
            \<and> idl_vars s'' = idl_vars s - {v}" for \<alpha>
            using idl by auto
          from step[of "\<lambda> _ . i"] have idl: "idl_state s'' (set vs)" 
            and vars: "idl_vars s'' = idl_vars s - {v}" by auto
          have ex2: "(\<exists>a. idl_state_sat s'' a) = (\<exists>a. idl_state_sat s a)" (is "?l = ?r")
          proof
            assume ?l
            then obtain \<alpha> where "idl_state_sat s'' \<alpha>" by auto
            with idl_vars[of s'', unfolded vars, OF _ idl, of \<alpha> ] 
            have "idl_state_sat s'' (\<alpha> (v := i))" by simp
            with step[of "\<alpha> (v := i)"] show ?r by auto
          next
            assume ?r
            with ex obtain \<alpha> where "idl_state_sat s \<alpha>" and "\<alpha> v = i" by auto
            with step[of \<alpha>] show ?l by auto
          qed
          from step[of "\<lambda> _ . i"] have idl: "idl_state s'' (set vs)" by auto
          note IH = Cons(1)[OF this res]
          thus ?thesis unfolding ex2 by auto
        qed
      next
        case False
        with res have res: "clean_bnds s vs = res"  unfolding ints s by (cases nums, auto)
        from idl have idl: "idl_state s (set vs)" unfolding s idl_state.simps all_entries_eq_all_lookups
          using Some[unfolded ints] by force        
        from Cons(1)[OF idl res] show ?thesis .
      qed
    qed
  qed
qed

lemma clean_bnds_size: assumes "clean_bnds s xs = Inl s'" 
  shows "idl_size s' \<le> idl_size s" 
  using assms 
proof (induct s xs arbitrary: s' rule: clean_bnds.induct)
  case 1
  thus ?case by (auto split: if_splits)
next
  case (2 bnds c v vs s')
  show ?case
  proof (rule ccontr)
    assume not: "\<not> ?thesis" 
    note res = 2(4)[simplified]
    from not 2 obtain xs where look: "Mapping.lookup bnds v = Some xs" by (auto split: option.splits)
    note res = res[unfolded this, simplified]
    then obtain i ys where xs: "xs = i # ys" by (cases xs, auto)
    note res = res[unfolded this, simplified]
    note look = look[unfolded xs]
    note IH = 2(2-3)[OF look refl]
    show False
    proof (cases ys)
      case (Cons j zs)
      from xs look IH(2)[OF Cons, of s'] res not show False unfolding Cons list.simps by auto
    next
      case Nil
      with res obtain s2 where inst: "instantiate_var v i (IDL_State bnds c) = Some s2" 
        by (auto split: option.splits)
      from res[unfolded Nil inst] 
      have res: "clean_bnds s2 vs = Inl s'" by auto
      from IH(1)[OF Nil inst res] not res look instantiate_var_size[OF inst] 
      show False using Nil by auto
    qed
  qed
qed

(* flag determines whether to activate symmetry breaking; in this case we put singleton-constraints into the bounds,
     and these restrictions will then be propagated on the constraints via clean_bnds  *)
definition idl_init :: "bool \<Rightarrow> (('v \<times> 's) \<times> int) list  \<Rightarrow> (('v \<times> 's) \<times> 'v \<times> 's) list list \<Rightarrow> ('v \<times> 's) idl_solver_state + bool" where
  "idl_init sym_break bnds diffs = (let 
     scs = IDL_CS [] [] (map (map Var_Var) diffs)
     in (if sym_break then 
       (let
       sToV = Mapping.of_alist (map (\<lambda> (vs,b). (snd vs, vs)) bnds);
       sorts = remdups (map (snd o fst) bnds);
       chosenVs = map (the o Mapping.lookup sToV) sorts;
       sbnds = Mapping.of_alist (map (\<lambda> (vs,b). (vs, if Mapping.lookup sToV (snd vs) = Some vs then [b] else [0..b])) bnds)
       in clean_bnds (IDL_State sbnds scs) chosenVs)
       else Inl (IDL_State (Mapping.of_alist (map (map_prod id (\<lambda> b. [0..b])) bnds)) scs)))" 

lemma mapping_of_alist_subset: "Mapping.entries (Mapping.of_alist xs) \<subseteq> set xs"
  by (metis in_entriesD lookup_of_alist map_of_SomeD subrelI)
term idl_init
lemma idl_init: assumes "idl_init sym_break bnds diffs = res" 
  and "idl_input ((bnds, diffs) :: ('v,'s)idl_input)" 
shows "res = Inl state \<Longrightarrow> idl_state state {} \<and> idl_solvable (bnds, diffs) = Ex (idl_state_sat state)" 
  "res = Inr b \<Longrightarrow> b = idl_solvable (bnds, diffs)" 
proof - 
  let ?br = sym_break
  define sToV where "sToV = Mapping.of_alist (map (\<lambda> (vs,b). (snd vs, vs)) bnds)" 
  define sorts where "sorts = remdups (map (snd o fst) bnds)" 
  define chosenVs where "chosenVs = (if ?br then map (the o Mapping.lookup sToV) sorts else [])" 
  define bnd where "bnd vs b = (if ?br then (if Mapping.lookup sToV (snd vs) = Some vs then [b] else [0..b]) else [0..b])" for vs b
  define sbnds where "sbnds = Mapping.of_alist (map (\<lambda> (vs,b). (vs, bnd vs b)) bnds)" 
  define scs where "scs = IDL_CS [] [] (map (map Var_Var) diffs)" 
  define state1 where "state1 = IDL_State sbnds scs" 
  have res: "res = (if ?br then clean_bnds state1 chosenVs else Inl state1)" 
    unfolding assms(1)[symmetric] idl_init_def Let_def state1_def scs_def sbnds_def chosenVs_def sorts_def sToV_def bnd_def 
    by (cases ?br, auto intro!: arg_cong[of _ _ "Mapping.of_alist"] map_cong)
  note idl = assms(2)[unfolded idl_input_def split]
  have flatten: "idl_flat_cs scs = set (map (set o map Var_Var) diffs)" unfolding scs_def by auto
  have keys: "Mapping.keys sbnds = fst ` set bnds" unfolding sbnds_def keys_of_alist by force

  have map_fst: "map fst (map (\<lambda> (vs,b). (vs, bnd vs b)) bnds) = map fst bnds" by (induct bnds, auto)
  have entries: "Mapping.entries sbnds = (\<lambda> (v,b). (v, bnd v b)) ` set bnds" 
    unfolding sbnds_def 
    apply (subst entries_of_alist)
    subgoal unfolding map_fst using idl by blast
    subgoal by (induct bnds, auto)
    done

  have state1: "idl_state state1 (set chosenVs)"
    unfolding state1_def idl_state.simps idl_flat_vs_def flatten keys set_map entries
  proof (intro conjI subsetI ballI)
    fix x
    assume "x \<in> (\<Union>c\<in>(set \<circ> map Var_Var) ` set diffs. \<Union>a\<in>c. set (idlc_vars a))" 
    from this
    obtain v w where vw: "(v,w) \<in> set (concat diffs)" and x: "x \<in> set (idlc_vars (Var_Var (v,w)))" by force
    from vw have "{v,w} \<subseteq> fst ` set bnds" using idl by blast  
    thus "x \<in> fst ` set bnds" using x by auto
  next
    fix xb 
    assume "xb \<in> {(v, bnd v b) |. (v, b) \<in> set bnds}" 
    then obtain x b where mem: "(x,b) \<in> set bnds" and xb: "xb = (x,bnd x b)" by auto
    from idl mem have "0 \<le> b" by blast
    thus "case xb of (v, ints) \<Rightarrow> distinct ints \<and> (v \<in> set chosenVs \<or> ints \<noteq> [])" unfolding xb split
      by (auto simp: bnd_def)
  qed (insert idl, auto)

  have main: "idl_solvable (bnds, diffs) = Ex (idl_state_sat state1)" (is "?l = ?r")
  proof
    (* easy direction: r implies l *)
    assume ?r
    then obtain \<alpha> where "idl_state_sat state1 \<alpha>" by auto
    note sat = this[unfolded state1_def idl_state_sat.simps]
    show ?l unfolding idl_solvable_def split
    proof (intro exI[of _ \<alpha>] conjI ballI)
      fix c
      assume "c \<in> set diffs" 
      with flatten[unfolded set_map]
      have "(set \<circ> map Var_Var) c \<in> idl_flat_cs scs" by auto
      with sat[THEN conjunct2, unfolded idl_constraints_sat_def, rule_format, OF this]
      show "\<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w" by force
    next
      fix vb
      assume "vb \<in> set bnds" 
      then obtain v b where vb: "vb = (v,b)" and mem: "(v,b) \<in> set bnds" 
        by (metis surj_pair)
      with sat[THEN conjunct1, folded all_entries_eq_all_lookups, unfolded entries]
      have sat: "\<alpha> v \<in> set (bnd v b)" by auto
      from idl mem have b: "b \<ge> 0" by blast
      from sat b show "case vb of (v, b) \<Rightarrow> 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b" unfolding vb split bnd_def 
        by (auto split: if_splits)
    qed
  next
    (* the harder direction where we have to show that w.l.o.g. we can fix one variable of each sort *)
    assume ?l
    from this[unfolded idl_solvable_def split]
    obtain \<alpha> where sat_bnds: "\<And> v b. (v, b) \<in> set bnds \<Longrightarrow> 0 \<le> \<alpha> v \<and> \<alpha> v \<le> b" and 
      sat_diffs: "\<And> c. c \<in> set diffs \<Longrightarrow> \<exists>(v, w)\<in>set c. \<alpha> v \<noteq> \<alpha> w" by auto

    define vs :: "'s \<Rightarrow> ('v \<times> 's)" where "vs s = the (Mapping.lookup sToV s)" for s

    define sv\<alpha> :: "'s \<Rightarrow> int" where "sv\<alpha> s = \<alpha> (vs s)" for s
    define svb :: "'s \<Rightarrow> int" where "svb s = the (map_of bnds (vs s))" for s
    define \<beta> where "\<beta> = (\<lambda> (x,s). if \<alpha> (x,s) = sv\<alpha> s then svb s else if \<alpha> (x,s) = svb s then sv\<alpha> s else \<alpha> (x,s))" 

    have \<beta>_to_\<alpha>: "snd v = snd w \<Longrightarrow> \<beta> v = \<beta> w \<longleftrightarrow> \<alpha> v = \<alpha> w" for v w unfolding \<beta>_def
      by (cases v; cases w; auto)        
 
    show ?r unfolding state1_def idl_state_sat.simps idl_constraints_sat_def flatten set_map 
        all_entries_eq_all_lookups[symmetric] entries
    proof (intro exI[of _ \<beta>] conjI allI impI ballI, clarsimp)
      fix disj
      assume "disj \<in> (set \<circ> map Var_Var) ` set diffs" 
      then obtain c where c: "c \<in> set diffs" and disj: "disj = (set \<circ> map Var_Var) c" by auto
      from sat_diffs[OF c] obtain v w where vw: "(v,w) \<in> set c" and diff: "\<alpha> v \<noteq> \<alpha> w" by auto
      from c vw have "(v,w) \<in> set (concat diffs)" by auto 
      with idl have "snd v = snd w" by blast
      with diff \<beta>_to_\<alpha> have diff: "\<beta> v \<noteq> \<beta> w" by auto
      from vw disj have "Var_Var (v,w) \<in> disj" by auto
      with diff show "Bex disj (idlc_sat \<beta>)" by force
    next
      fix v s b
      assume mem: "((v,s),b) \<in> set bnds" 
      with idl have b: "b \<ge> 0" by force
      have snd: "snd (v,s) = s" by simp
      from mem have "s \<in> Mapping.keys sToV"  unfolding sToV_def keys_of_alist by force
      then obtain v' where v': "Mapping.lookup sToV s = Some v'" by (meson in_keysD)
      hence "(s,v') \<in> Mapping.entries sToV" by (rule in_entriesI)
      from set_mp[OF mapping_of_alist_subset  this[unfolded sToV_def]] obtain b' 
        where vb': "(v',b') \<in> set bnds" and snd_v': "snd v' = s" by auto
      with idl mem snd have "b' = b" by blast
      with vb' have vb': "(v',b) \<in> set bnds" by auto
      from v' have vsv': "vs s = v'" unfolding vs_def by simp
      have svbs: "svb s = b" unfolding svb_def vsv' using vb' idl[THEN conjunct1] by simp
      show "\<beta> (v,s) \<in> set (bnd (v,s) b)" 
      proof (cases "Mapping.lookup sToV s = Some (v, s)")
        case True
        hence vss: "vs s = (v,s)" unfolding vs_def by simp
        hence "\<beta> (v,s) = svb s" unfolding \<beta>_def split sv\<alpha>_def by simp
        also have "svb s = b" by fact
        finally show ?thesis unfolding bnd_def using True b by simp
      next
        case False
        hence set: "set (bnd (v, s) b) = {0..b}" 
          unfolding bnd_def by auto
        from sat_bnds[OF vb'] 
        have "sv\<alpha> s \<in> {0..b}" unfolding sv\<alpha>_def vsv' by auto
        moreover 
        from sat_bnds[OF mem] 
        have "\<alpha> (v,s) \<in> {0..b}" by auto
        moreover 
        from b svbs have "svb s \<in> {0..b}" by auto
        ultimately
        show ?thesis unfolding set \<beta>_def split by auto
      qed
    qed
  qed

  have chosen: "\<not> ?br \<Longrightarrow> set chosenVs = {}" by (auto simp: chosenVs_def)
  note clean = clean_bnds[OF state1 refl]
  show "res = Inl state \<Longrightarrow> res = Inl state \<Longrightarrow> idl_state state {} \<and> idl_solvable (bnds, diffs) = Ex (idl_state_sat state)" 
    using res clean(2)[of state] state1 chosen unfolding main by (cases ?br; force)
  show "res = Inr b \<Longrightarrow> b = idl_solvable (bnds, diffs)"
    using res clean(1)[of b] unfolding main by (cases ?br; force)
qed



(* assume, that we get a structured problem as input; returns a structured problem *)
definition deduction_step :: "'v idl_solver_state \<Rightarrow> 'v idl_solver_state + bool" where
  "deduction_step s = (case idl_delete_vi s of 
     (s1,vs) \<Rightarrow> (case clean_bnds s1 vs of
       Inr b \<Rightarrow> Inr b
     | Inl s2 \<Rightarrow> (case idl_restructure s2 of
        None \<Rightarrow> Inr False
      | Some s3 \<Rightarrow> Inl s3)))" 

lemma deduction_step: assumes idl: "idl_state s {}" 
  and res: "deduction_step s = res" 
shows "res = Inr b \<Longrightarrow> b = (Ex (idl_state_sat s))" 
  "res = Inl s' \<Longrightarrow> idl_state s' {} \<and> Ex (idl_state_sat s') = Ex (idl_state_sat s)" 
proof (atomize(full), goal_cases)
  case 1
  obtain s1 vs where del: "idl_delete_vi s = (s1,vs)" by force
  note res = res[unfolded deduction_step_def del split]
  from idl_delete_vi[OF del idl]
  have idl: "idl_state s1 (set vs)" and 
    eq: "Ex (idl_state_sat s) = Ex (idl_state_sat s1)" by auto
  show ?case
  proof (cases "clean_bnds s1 vs")
    case (Inr r)
    from clean_bnds(1)[OF idl Inr refl] Inr res eq show ?thesis by auto
  next
    case (Inl s2)
    from clean_bnds(2)[OF idl Inl refl] eq
    have idl: "idl_state s2 {}" and eq: "Ex (idl_state_sat s) = Ex (idl_state_sat s2)"
       by auto
    note res = res[unfolded Inl sum.simps]
    show ?thesis
    proof (cases "idl_restructure s2")
      case None
      from idl_restructure(1)[OF None] eq res None show ?thesis by auto
    next
      case (Some s3)
      from idl_restructure(2-)[OF Some] eq idl Some res show ?thesis by auto
    qed
  qed
qed

lemma deduction_step_size: assumes "deduction_step s = Inl s'" 
  shows "idl_size s' \<le> idl_size s" 
  using assms unfolding deduction_step_def
  by (auto split: prod.splits sum.splits option.splits
    dest!: clean_bnds_size idl_delete_vi_size idl_restructure)

fun deduction_steps_main :: "nat \<Rightarrow> 'v idl_solver_state \<Rightarrow> 'v idl_solver_state + bool" where
  "deduction_steps_main n s = (case deduction_step s of
     Inr b \<Rightarrow> Inr b
   | Inl s' \<Rightarrow> let n' = idl_size s' in if n' < n then deduction_steps_main n' s' else Inl s')"

declare deduction_steps_main.simps[simp del]

definition "deduction_steps s = deduction_steps_main (idl_size s) s" 

lemma deduction_steps: assumes idl: "idl_state s {}" 
  and res: "deduction_steps s = res" 
shows "res = Inr b \<Longrightarrow> b = (Ex (idl_state_sat s))" 
  "res = Inl s' \<Longrightarrow> idl_state s' {} \<and> Ex (idl_state_sat s') = Ex (idl_state_sat s)" 
proof (atomize(full), goal_cases)
  case 1
  from assms show ?case unfolding deduction_steps_def
  proof (induct s rule: measure_induct[of idl_size])
    case (1 s)
    note res = 1(3)[unfolded deduction_steps_main.simps[of _ s]]
    note IH = 1(1)
    note idl = 1(2)
    note ded = deduction_step[OF idl refl]
    show ?case
    proof (cases "deduction_step s")
      case (Inr b)
      from ded(1)[OF this] res Inr show ?thesis by auto
    next
      case (Inl s1)
      note res = res[unfolded Inl sum.simps Let_def]
      from ded(2)[OF Inl] 
      have idl: "idl_state s1 {}" 
        and eq: "Ex (idl_state_sat s) = Ex (idl_state_sat s1)" by auto
      show ?thesis
      proof (cases "idl_size s1 < idl_size s")
        case True
        with res have res: "deduction_steps_main (idl_size s1) s1 = res" by auto
        from IH[rule_format, OF True idl res] 
        show ?thesis unfolding eq by auto
      next
        case False
        with res eq idl show ?thesis by auto
      qed
    qed
  qed
qed

lemma deduction_steps_size: assumes "deduction_steps s = Inl s'" 
  shows "idl_size s' \<le> idl_size s" 
  using assms unfolding deduction_steps_def
proof (induct s arbitrary: s' rule: measure_induct[of idl_size])
  case (1 s s')
  thus ?case unfolding deduction_steps_main.simps[of _ s] Let_def
    by (auto split: sum.splits if_splits dest: deduction_step_size)
qed

fun idl_var_int where
  "idl_var_int (Var_Int vi) = (fst vi, Some (snd vi))" 
| "idl_var_int (Var_Var vw) = (fst vw, None)" 

fun idl_find_var :: "'v idl_solver_state \<Rightarrow> ('v \<times> int option) + bool" where
  "idl_find_var (IDL_State bnds (IDL_CS vis vws cs)) = (
    case vis of 
      vi # vis2 \<Rightarrow> Inl (map_prod id Some vi)
    | _ \<Rightarrow> (case vws of vw # vws2 \<Rightarrow> Inl (fst vw, None)
    | _ \<Rightarrow> (case cs of [] \<Rightarrow> Inr True
    | c # cs2 \<Rightarrow> (case c of [] \<Rightarrow> Inr False | a # as \<Rightarrow> Inl (idl_var_int a)))))" 

fun reorder :: "int option \<Rightarrow> int list \<Rightarrow> int list" where
  "reorder None xs = xs" 
| "reorder (Some i) xs = (case span ((<) i) xs of
     (bef, j # aft) \<Rightarrow> if i = j then bef @ aft @ [j] else xs
    | _ \<Rightarrow> xs)" 

lemma set_reorder[simp]: "set (reorder io xs) = set xs" 
proof (cases io)
  case (Some i)
  obtain bef aft where spa: "span ((<) i) xs = (bef,aft)" by force
  from this[symmetric, unfolded span]
  have "set xs = set bef \<union> set aft" by simp 
    (metis set_append takeWhile_dropWhile_id)
  thus ?thesis unfolding Some reorder.simps spa
    by (auto split: list.splits)
qed auto

definition "finite_mapping m = finite (Mapping.keys m)" 

lemma finite_mapping_code[code]: "finite_mapping (Mapping m) = True" 
  unfolding finite_mapping_def 
  by (simp add: keys_Mapping)
  

function idl_main_solver :: "'v idl_solver_state \<Rightarrow> bool" where
  "idl_main_solver s = (case idl_restructure s of None \<Rightarrow> False 
   | Some s1 \<Rightarrow> (case deduction_steps s1 of
     Inr b \<Rightarrow> b
   | Inl s2 \<Rightarrow> (case idl_find_var s2 of 
     Inr b \<Rightarrow> b
   | Inl (v,io) \<Rightarrow> (case s2 of IDL_State bnds cs \<Rightarrow>
       if finite_mapping bnds then 
       (case Mapping.lookup bnds v of
          Some ints \<Rightarrow> Bex (set (reorder io ints)) (\<lambda> i. map_option idl_main_solver (instantiate_var v i s2) = Some True)
           ) else Code.abort (STR ''infinite bnds are not allowed'') ( \<lambda> _. True)))))" 
  by pat_completeness auto

termination 
proof (standard, rule wf_measure[of idl_size], goal_cases)
  case (1 s s1 s2 vo v io bnds cs ints i s3)
  from 1 have fin: "finite (Mapping.keys bnds)" 
    by (auto simp: finite_mapping_def)
  from 1 have "v \<in> Mapping.keys bnds" by (auto simp add: keys_dom_lookup)
  hence "Mapping.keys (Mapping.delete v bnds) \<subset> Mapping.keys bnds" by auto
  with 1 fin have lt: "Mapping.size (Mapping.delete v bnds) < Mapping.size bnds" 
    unfolding Mapping.size_def by (simp add: psubset_card_mono)
  have "idl_size s3 = Mapping.size (Mapping.delete v bnds)" 
    using 1(9) unfolding 1(5) 
    by (cases cs, auto split: if_splits option.splits simp: Let_def)
  also have "\<dots> < idl_size s2" using lt unfolding 1 by simp
  also have "\<dots> \<le> idl_size s1" using deduction_steps_size[OF 1(2)] .
  also have "\<dots> \<le> idl_size s" using idl_restructure(2-)[OF 1(1)] by auto
  finally show ?case by auto
qed

declare idl_main_solver.simps[simp del]

lemma idl_main_solver: assumes "idl_state s {}" 
  shows "idl_main_solver s = Ex (idl_state_sat s)" 
  using assms
proof (induct s rule: idl_main_solver.induct)
  case (1 s)
  note idl = 1(2)
  note IH = 1(1)
  note res = idl_main_solver.simps[of s]
  show ?case
  proof (cases "idl_restructure s")
    case None
    with res idl_restructure[of s] show ?thesis by auto
  next
    case (Some s1)
    note res = res[unfolded Some option.simps]
    note IH = IH[OF Some]
    from idl idl_restructure(2-)[OF Some]
    have eq: "idl_state_sat s = idl_state_sat s1" 
      and idl: "idl_state s1 {}" by auto
    show ?thesis
    proof (cases "deduction_steps s1")
      case (Inr b)
      from deduction_steps(1)[OF idl Inr refl] res[unfolded Inr] eq show ?thesis by auto
    next
      case (Inl s2)
      note res = res[unfolded Inl sum.simps]
      note IH = IH[OF Inl]
      from deduction_steps(2)[OF idl Inl refl] eq
      have idl: "idl_state s2 {}" and eq: "Ex (idl_state_sat s) = Ex (idl_state_sat s2)" by auto
      obtain bnds diffs where s2: "s2 = IDL_State bnds diffs" by (cases s2, auto)
      obtain vis vws cs where diffs: "diffs = IDL_CS vis vws cs" by (cases diffs, auto)
      show ?thesis
      proof (cases "idl_find_var s2")
        case (Inr b)
        with res have res: "idl_main_solver s = b" by auto
        show ?thesis
        proof (cases b)
          case True
          with Inr have "idl_cs_empty s2" unfolding s2 diffs
            by (auto split: list.splits)
          from idl_cs_empty[OF idl this] res True show ?thesis using eq by auto
        next
          case False
          with Inr obtain cs' where "cs = [] # cs'" unfolding s2 diffs
            by (auto split: list.splits)
          hence "\<not> Ex (idl_state_sat s2)" 
            unfolding s2 diffs by (auto simp: idl_constraints_sat_def)
          with eq False res show ?thesis by auto
        qed
      next
        case (Inl vo)
        then obtain v io where Inl: "idl_find_var s2 = Inl (v,io)" by (cases vo, auto)
        from idl[unfolded s2] 
        have fin: "finite (Mapping.keys bnds)" by auto
        from Inl have "v \<in> idl_flat_vs diffs" unfolding s2 diffs idl_flat_vs_def idl_flat_cs.simps singleton_def
          by (cases "hd (hd cs)", auto split: list.splits)
        with idl[unfolded s2] have v: "v \<in> Mapping.keys bnds" by auto
        from fin have finm: "finite_mapping bnds" unfolding finite_mapping_def by auto 
        hence "finite_mapping bnds = True" by simp
        note res = res[unfolded Inl sum.simps split, unfolded s2 idl_solver_state.simps, folded s2, unfolded this if_True]
        from v obtain ints where look: "Mapping.lookup bnds v = Some ints"
          by (meson in_keysD)
        note IH = IH[OF Inl refl s2 finm look, unfolded set_reorder]
        note res = res[unfolded look option.simps split]
        from idl have idlv: "idl_state s2 (insert v {})" unfolding s2 by auto
        show ?thesis 
        proof
          assume "idl_main_solver s" 
          from this[unfolded res split]
          obtain i s3 where i: "i \<in> set ints" 
            and inst: "instantiate_var v i s2 = Some s3" 
            and res: "idl_main_solver s3 = True" by auto
          from instantiate_var(2)[OF _ look i, of _ diffs, folded s2, OF _ inst idlv refl]
          have inst': "\<alpha> v = i \<Longrightarrow> idl_state s3 {} \<and> idl_state_sat s2 \<alpha> = idl_state_sat s3 \<alpha> \<and> v \<notin> idl_vars s3" 
            for \<alpha> by auto
          from inst'[of "\<lambda> _. i"] have idl3: "idl_state s3 {}" and v: "v \<notin> idl_vars s3" by auto
          from IH[OF i inst idl3] res obtain \<alpha> where "idl_state_sat s3 \<alpha>" by auto
          with idl_vars[of s3 \<alpha>, OF _ idl3] v 
          have sat: "idl_state_sat s3 (\<alpha> (v := i))" by force
          with inst'[of "\<alpha> (v := i)"] have "Ex (idl_state_sat s2)" by auto
          with eq show "Ex (idl_state_sat s)" by auto
        next
          assume "Ex (idl_state_sat s)" 
          with eq obtain \<alpha> where sat: "idl_state_sat s2 \<alpha>" by auto
          from this[unfolded s2 idl_state_sat.simps] look 
          have mem: "\<alpha> v \<in> set ints" by auto
          note inst = instantiate_var[OF _ look mem, of \<alpha> diffs, folded s2, OF refl refl idlv]
          from sat inst(1) obtain s3 where instSome: "instantiate_var v (\<alpha> v) s2 = Some s3" 
            by auto
          from inst(2)[OF instSome] sat
          have idl3: "idl_state s3 {}" and sat: "idl_state_sat s3 \<alpha>" by auto
          from IH[OF mem instSome idl3] sat 
          have IH: "idl_main_solver s3 = True" by auto
          show "idl_main_solver s" unfolding res using mem instSome IH by auto
        qed
      qed
    qed
  qed
qed

definition "inner_solver sym_break bnds diffs = (case idl_init sym_break bnds diffs 
   of Inl s \<Rightarrow> idl_main_solver s | Inr b \<Rightarrow> b)" 

lemma inner_solver: "idl_smt_solver (inner_solver sym_break)" 
  unfolding inner_solver_def idl_smt_solver_alt_def
proof (intro allI impI, goal_cases)
  case (1 bnds diffs)
  show ?case
  proof (cases "idl_init sym_break bnds diffs")
    case (Inr b)
    from idl_init(2)[OF refl 1 Inr] Inr show ?thesis by auto
  next
    case (Inl s)
    from idl_init(1)[OF refl 1 Inl] Inl idl_main_solver[of s]
    show ?thesis by auto
  qed
qed

definition "parametric_idl_solver sort_pre_process sym_break = (if sort_pre_process then
    idl_pre_processor (inner_solver sym_break) else inner_solver sym_break)" 

lemma parametric_idl_solver: "idl_smt_solver (parametric_idl_solver sort_pp sym_break)" 
  unfolding parametric_idl_solver_def using inner_solver idl_pre_processor by auto

definition "default_idl_solver = parametric_idl_solver True True" 

lemma default_idl_solver: "idl_smt_solver default_idl_solver" 
  unfolding default_idl_solver_def by (rule parametric_idl_solver)

end
