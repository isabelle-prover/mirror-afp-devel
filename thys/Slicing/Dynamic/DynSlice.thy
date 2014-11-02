section {* Dynamic Backward Slice *}

theory DynSlice imports DependentLiveVariables BitVector "../Basic/SemanticsCFG" begin

subsection {* Backward slice of paths *}

context DynPDG begin

fun slice_path :: "'edge list \<Rightarrow> bit_vector"
  where "slice_path [] = []"
  | "slice_path (a#as) = (let n' = last(targetnodes (a#as)) in
                           (sourcenode a -a#as\<rightarrow>\<^sub>d* n')#slice_path as)"

(*<*)declare Let_def [simp](*>*)

lemma slice_path_length:
  "length(slice_path as) = length as"
by(induct as) auto


lemma slice_path_right_Cons:
  assumes slice:"slice_path as = x#xs"
  obtains a' as' where "as = a'#as'" and "slice_path as' = xs"
proof(atomize_elim)
  from slice show "\<exists>a' as'. as = a'#as' \<and> slice_path as' = xs"
    by(induct as) auto
qed


subsection {* The proof of the fundamental property of (dynamic) slicing *}

fun select_edge_kinds :: "'edge list \<Rightarrow> bit_vector \<Rightarrow> 'state edge_kind list"
where "select_edge_kinds [] [] = []"
  | "select_edge_kinds (a#as) (b#bs) = (if b then kind a
      else (case kind a of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>))#select_edge_kinds as bs"


definition slice_kinds :: "'edge list \<Rightarrow> 'state edge_kind list"
  where "slice_kinds as = select_edge_kinds as (slice_path as)"


lemma select_edge_kinds_max_bv:
  "select_edge_kinds as (replicate (length as) True) = kinds as"
by(induct as,auto simp:kinds_def)


lemma slice_path_leqs_information_same_Uses:
  "\<lbrakk>n -as\<rightarrow>* n'; bs \<preceq>\<^sub>b bs'; slice_path as = bs;
    select_edge_kinds as bs = es; select_edge_kinds as bs' = es'; 
    \<forall>V xs. (V,xs,as) \<in> dependent_live_vars n' \<longrightarrow> state_val s V = state_val s' V;
    preds es' s'\<rbrakk> 
  \<Longrightarrow> (\<forall>V \<in> Use n'. state_val (transfers es s) V =
      state_val (transfers es' s') V) \<and> preds es s"
proof(induct bs bs' arbitrary:as es es' n s s' rule:bv_leqs.induct)
  case 1
  from `slice_path as = []` have "as = []" by(cases as) auto
  with `select_edge_kinds as [] = es` `select_edge_kinds as [] = es'`
  have "es = []" and "es' = []" by simp_all
  { fix V assume "V \<in> Use n'"
    hence "(V,[],[]) \<in> dependent_live_vars n'" by(rule dep_vars_Use)
    with `\<forall>V xs. (V,xs,as) \<in> dependent_live_vars n' \<longrightarrow>
                  state_val s V = state_val s' V` `V \<in> Use n'` `as = []`
    have "state_val s V = state_val s' V" by blast }
  with `es = []` `es' = []` show ?case by simp
next
  case (2 x xs y ys)
  note all = `\<forall>V xs. (V,xs,as) \<in> dependent_live_vars n' \<longrightarrow>
                     state_val s V = state_val s' V`
  note IH = `\<And>as es es' n s s'. \<lbrakk>n -as\<rightarrow>* n'; xs \<preceq>\<^sub>b ys; slice_path as = xs; 
                        select_edge_kinds as xs = es; select_edge_kinds as ys = es';
                        \<forall>V xs. (V,xs,as) \<in> dependent_live_vars n' \<longrightarrow>
                                   state_val s V = state_val s' V; 
                           preds es' s'\<rbrakk>
            \<Longrightarrow> (\<forall>V \<in> Use n'. state_val (transfers es s) V =
                state_val (transfers es' s') V) \<and> preds es s`
  from `x#xs \<preceq>\<^sub>b y#ys` have "x \<longrightarrow> y" and "xs \<preceq>\<^sub>b ys" by simp_all
  from `slice_path as = x#xs` obtain a' as' where "as = a'#as'"
    and "slice_path as' = xs" by(erule slice_path_right_Cons)
  from `as = a'#as'` `select_edge_kinds as (x#xs) = es`
  obtain ex esx where "es = ex#esx"
    and ex:"ex = (if x then kind a'
                    else (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>))"
    and "select_edge_kinds as' xs = esx" by auto
  from `as = a'#as'` `select_edge_kinds as (y#ys) = es'` obtain ex' esx' 
    where "es' = ex'#esx'"
    and ex':"ex' = (if y then kind a'
                    else (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>))"
    and "select_edge_kinds as' ys = esx'" by auto
  from `n -as\<rightarrow>* n'` `as = a'#as'` have [simp]:"n = sourcenode a'" 
    and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(auto elim:path_split_Cons)
  from `n -as\<rightarrow>* n'` `as = a'#as'` have "last(targetnodes as) = n'"
    by(fastforce intro:path_targetnode)
  from `preds es' s'` `es' = ex'#esx'` have "pred ex' s'"
    and "preds esx' (transfer ex' s')" by simp_all
  show ?case
  proof(cases "as' = []")
    case True
    hence [simp]:"as' = []" by simp
    with `slice_path as' = xs` `xs \<preceq>\<^sub>b ys` 
    have [simp]:"xs = [] \<and> ys = []" by auto(cases ys,auto)+
    with `select_edge_kinds as' xs = esx` `select_edge_kinds as' ys = esx'`
    have [simp]:"esx = []" and [simp]:"esx' = []" by simp_all
    from True `targetnode a' -as'\<rightarrow>* n'` 
    have [simp]:"n' = targetnode a'" by(auto elim:path.cases)
    show ?thesis
    proof(cases x)
      case True
      with `x \<longrightarrow> y` ex ex' have [simp]:"ex = kind a' \<and> ex' = kind a'" by simp
      have "pred ex s"
      proof(cases ex)
        case (Predicate Q)
        with ex ex' True `x \<longrightarrow> y` have [simp]:"transfer ex s = s" 
          and [simp]:"transfer ex' s' = s'"
          by(cases "kind a'",auto)+
        show ?thesis
        proof(cases "n -[a']\<rightarrow>\<^bsub>cd\<^esub> n'")
          case True
          { fix V' assume "V' \<in> Use n"
            with True `valid_edge a'`
            have "(V',[],a'#[]@[]) \<in> dependent_live_vars n'"
              by(fastforce intro:dep_vars_Cons_cdep DynPDG_path_Nil 
                          simp:targetnodes_def)
            with all `as = a'#as'` have "state_val s V' = state_val s' V'"
              by fastforce }
          with `pred ex' s'` `valid_edge a'`
          show ?thesis by(fastforce elim:CFG_edge_Uses_pred_equal)
        next
          case False
          from ex True Predicate have "kind a' = (Q)\<^sub>\<surd>" by(auto split:split_if_asm)
          from True `slice_path as = x#xs` `as = a'#as'` have "n -[a']\<rightarrow>\<^sub>d* n'"
            by(auto simp:targetnodes_def)
          thus ?thesis
          proof(induct rule:DynPDG_path.cases)
            case (DynPDG_path_Nil nx)
            hence False by simp
            thus ?case by simp
          next
            case (DynPDG_path_Append_cdep nx asx n'' asx' nx')
            from `[a'] = asx@asx'` 
            have "(asx = [a'] \<and> asx' = []) \<or> (asx = [] \<and> asx' = [a'])"
              by (cases asx) auto
            hence False
            proof
              assume "asx = [a'] \<and> asx' = []"
              with `n'' -asx'\<rightarrow>\<^bsub>cd\<^esub> nx'` show False
                by(fastforce elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
            next
              assume "asx = [] \<and> asx' = [a']"
              with `nx -asx\<rightarrow>\<^sub>d* n''` have "nx = n''" and "asx' = [a']"
                by(auto intro:DynPDG_empty_path_eq_nodes)
              with `n = nx` `n' = nx'` `n'' -asx'\<rightarrow>\<^bsub>cd\<^esub> nx'` False
              show False by simp
            qed
            thus ?thesis by simp
          next
            case (DynPDG_path_Append_ddep nx asx n'' V asx' nx')
            from `[a'] = asx@asx'` 
            have "(asx = [a'] \<and> asx' = []) \<or> (asx = [] \<and> asx' = [a'])"
              by (cases asx) auto
            thus ?case
            proof
              assume "asx = [a'] \<and> asx' = []"
              with `n'' -{V}asx'\<rightarrow>\<^bsub>dd\<^esub> nx'` have False
                by(fastforce elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
              thus ?thesis by simp
            next
              assume "asx = [] \<and> asx' = [a']"
              with `nx -asx\<rightarrow>\<^sub>d* n''` have "nx = n''"
                by(simp add:DynPDG_empty_path_eq_nodes)
              { fix V' assume "V' \<in> Use n"
                from `n'' -{V}asx'\<rightarrow>\<^bsub>dd\<^esub> nx'` `asx = [] \<and> asx' = [a']` `n' = nx'`
                have "(V,[],[]) \<in> dependent_live_vars n'"
                  by(fastforce intro:dep_vars_Use elim:DynPDG_edge.cases
                    simp:dyn_data_dependence_def)
                with `V' \<in> Use n` `n'' -{V}asx'\<rightarrow>\<^bsub>dd\<^esub> nx'` `asx = [] \<and> asx' = [a']`
                  `n = nx` `nx = n''` `n' = nx'`
                have "(V',[],[a']) \<in> dependent_live_vars n'"
                  by(auto elim:dep_vars_Cons_ddep simp:targetnodes_def)
                with all `as = a'#as'` have "state_val s V' = state_val s' V'"
                  by fastforce }
              with `pred ex' s'` `valid_edge a'` ex ex' True `x \<longrightarrow> y` show ?thesis
                by(fastforce elim:CFG_edge_Uses_pred_equal)
            qed
          qed
        qed
      qed simp
      { fix V assume "V \<in> Use n'"
        from `V \<in> Use n'` have "(V,[],[]) \<in> dependent_live_vars n'" 
          by(rule dep_vars_Use)
        have "state_val (transfer ex s) V = state_val (transfer ex' s') V"
        proof(cases "n -{V}[a']\<rightarrow>\<^bsub>dd\<^esub> n'")
          case True
          hence "V \<in> Def n"
            by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
          have "\<And>V. V \<in> Use n \<Longrightarrow> state_val s V = state_val s' V"
          proof -
            fix V' assume "V' \<in> Use n"
            with `(V,[],[]) \<in> dependent_live_vars n'` True
            have "(V',[],[a']) \<in> dependent_live_vars n'"
              by(fastforce intro:dep_vars_Cons_ddep simp:targetnodes_def)
            with all `as = a'#as'` show "state_val s V' = state_val s' V'" by auto
          qed
          with `valid_edge a'` `pred ex' s'` `pred ex s`
          have "\<forall>V \<in> Def n. state_val (transfer (kind a') s) V =
                              state_val (transfer (kind a') s') V"
            by simp(rule CFG_edge_transfer_uses_only_Use,auto)
          with `V \<in> Def n` have "state_val (transfer (kind a') s) V = 
                         state_val (transfer (kind a') s') V"
            by simp
          thus ?thesis by fastforce
        next
          case False
          with `last(targetnodes as) = n'` `as = a'#as'`
            `(V,[],[]) \<in> dependent_live_vars n'`
          have "(V,[a'],[a']) \<in> dependent_live_vars n'"
            by(fastforce intro:dep_vars_Cons_keep)
          from `(V,[a'],[a']) \<in> dependent_live_vars n'` all `as = a'#as'`
          have states_eq:"state_val s V = state_val s' V"
            by auto
          from `valid_edge a'` `V \<in> Use n'` False `pred ex s`
          have "state_val (transfers (kinds [a']) s) V = state_val s V"
            apply(auto intro!:no_ddep_same_state path_edge simp:targetnodes_def)
            apply(simp add:kinds_def)
            by(case_tac as',auto)
          moreover
          from `valid_edge a'` `V \<in> Use n'` False `pred ex' s'`
          have "state_val (transfers (kinds [a']) s') V = state_val s' V"
            apply(auto intro!:no_ddep_same_state path_edge simp:targetnodes_def)
            apply(simp add:kinds_def)
            by(case_tac as',auto)
          ultimately show ?thesis using states_eq by(auto simp:kinds_def)
        qed }
      hence "\<forall>V \<in> Use n'. state_val (transfer ex s) V = 
                                state_val (transfer ex' s') V" by simp
      with `pred ex s` `es = ex#esx` `es' = ex'#esx'` show ?thesis by simp
    next
      case False
      with ex have cases_x:"ex = (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>)"
        by simp
      from cases_x have "pred ex s" by(cases "kind a'",auto)
      show ?thesis
      proof(cases y)
        case True
        with ex' have [simp]:"ex' = kind a'" by simp
        { fix V assume "V \<in> Use n'"
          from `V \<in> Use n'` have "(V,[],[]) \<in> dependent_live_vars n'"
            by(rule dep_vars_Use)
          from `slice_path as = x#xs` `as = a'#as'` `\<not> x` 
          have "\<not> n -[a']\<rightarrow>\<^sub>d* n'" by(simp add:targetnodes_def)
          hence "\<not> n -{V}[a']\<rightarrow>\<^bsub>dd\<^esub> n'" by(fastforce dest:DynPDG_path_ddep)
          with `last(targetnodes as) = n'` `as = a'#as'`
            `(V,[],[]) \<in> dependent_live_vars n'`
          have "(V,[a'],[a']) \<in> dependent_live_vars n'"
            by(fastforce intro:dep_vars_Cons_keep)
          with all `as = a'#as'` have "state_val s V = state_val s' V" by auto
          from `valid_edge a'` `V \<in> Use n'` `pred ex' s'`
            `\<not> n -{V}[a']\<rightarrow>\<^bsub>dd\<^esub> n'` `last(targetnodes as) = n'` `as = a'#as'`
          have "state_val (transfers (kinds [a']) s') V = state_val s' V"
            apply(auto intro!:no_ddep_same_state path_edge)
            apply(simp add:kinds_def)
            by(case_tac as',auto)
          with `state_val s V = state_val s' V` cases_x
          have "state_val (transfer ex s) V =
                state_val (transfer ex' s') V"
            by(cases "kind a'",simp_all add:kinds_def) }
        hence "\<forall>V \<in> Use n'. state_val (transfer ex s) V =
                           state_val (transfer ex' s') V" by simp
        with `as = a'#as'` `es = ex#esx` `es' = ex'#esx'` `pred ex s` 
        show ?thesis by simp
      next
        case False
        with ex' have cases_y:"ex' = (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>)"
          by simp
        with cases_x have [simp]:"ex = ex'" by(cases "kind a'") auto
        { fix V assume "V \<in> Use n'"
          from `V \<in> Use n'` have "(V,[],[]) \<in> dependent_live_vars n'"
            by(rule dep_vars_Use)
          from `slice_path as = x#xs` `as = a'#as'` `\<not> x` 
          have "\<not> n -[a']\<rightarrow>\<^sub>d* n'" by(simp add:targetnodes_def)
          hence no_dep:"\<not> n -{V}[a']\<rightarrow>\<^bsub>dd\<^esub> n'" by(fastforce dest:DynPDG_path_ddep)
          with `last(targetnodes as) = n'` `as = a'#as'`
            `(V,[],[]) \<in> dependent_live_vars n'`
          have "(V,[a'],[a']) \<in> dependent_live_vars n'"
            by(fastforce intro:dep_vars_Cons_keep)
          with all `as = a'#as'` have "state_val s V = state_val s' V" by auto }
        with `as = a'#as'` cases_x `es = ex#esx` `es' = ex'#esx'` `pred ex s`
        show ?thesis by(cases "kind a'",auto)
      qed
    qed
  next
    case False
    show ?thesis
    proof(cases "\<forall>V xs. (V,xs,as') \<in> dependent_live_vars n' \<longrightarrow>
                        state_val (transfer ex s) V = state_val (transfer ex' s') V")
      case True
      hence imp':"\<forall>V xs. (V,xs,as') \<in> dependent_live_vars n' \<longrightarrow>
                       state_val (transfer ex s) V = state_val (transfer ex' s') V" .
      from IH[OF `targetnode a' -as'\<rightarrow>* n'` `xs \<preceq>\<^sub>b ys` `slice_path as' = xs`
        `select_edge_kinds as' xs = esx` `select_edge_kinds as' ys = esx'` 
        this `preds esx' (transfer ex' s')`]
      have all':"\<forall>V\<in>Use n'. state_val (transfers esx (transfer ex s)) V =
                             state_val (transfers esx' (transfer ex' s')) V"
        and "preds esx (transfer ex s)" by simp_all
      have "pred ex s"
      proof(cases ex)
        case (Predicate Q)
        with `slice_path as = x#xs` `as = a'#as'` `last(targetnodes as) = n'` ex 
        have "ex = (\<lambda>s. True)\<^sub>\<surd> \<or> n -a'#as'\<rightarrow>\<^sub>d* n'"
          by(cases "kind a'",auto split:split_if_asm) 
        thus ?thesis
        proof
          assume "ex = (\<lambda>s. True)\<^sub>\<surd>" thus ?thesis by simp
        next
          assume "n -a'#as'\<rightarrow>\<^sub>d* n'"
          with `slice_path as = x#xs` `as = a'#as'` `last(targetnodes as) = n'` ex
          have [simp]:"ex = kind a'" by clarsimp
          with `x \<longrightarrow> y` ex ex' have [simp]:"ex' = ex" by(cases x) auto
          from `n -a'#as'\<rightarrow>\<^sub>d* n'` show ?thesis
          proof(induct rule:DynPDG_path_rev_cases)
            case DynPDG_path_Nil
            hence False by simp
            thus ?thesis by simp
          next
            case (DynPDG_path_cdep_Append n'' asx asx')
            from `n -asx\<rightarrow>\<^bsub>cd\<^esub> n''`have "asx \<noteq> []"
              by(auto elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
            with `n -asx\<rightarrow>\<^bsub>cd\<^esub> n''` `n'' -asx'\<rightarrow>\<^sub>d* n'` `a'#as' = asx@asx'`
            have cdep:"\<exists>as1 as2 n''. n -a'#as1\<rightarrow>\<^bsub>cd\<^esub> n'' \<and> 
                                     n'' -as2\<rightarrow>\<^sub>d* n' \<and> as' = as1@as2"
              by(cases asx) auto 
            { fix V assume "V \<in> Use n"
              with cdep `last(targetnodes as) = n'` `as = a'#as'`
              have "(V,[],as) \<in> dependent_live_vars n'"
                by(fastforce intro:dep_vars_Cons_cdep)
              with all have "state_val s V = state_val s' V" by blast }
            with `valid_edge a'` `pred ex' s'`
            show ?thesis by(fastforce elim:CFG_edge_Uses_pred_equal)
          next
            case (DynPDG_path_ddep_Append V n'' asx asx')
            from `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` obtain ai ais where "asx = ai#ais"
              by(cases asx)(auto dest:DynPDG_ddep_edge_CFG_path)
            with `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` have "sourcenode ai = n"
              by(fastforce dest:DynPDG_ddep_edge_CFG_path elim:path.cases)
            from `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` `asx = ai#ais`
            have "last(targetnodes asx) = n''"
              by(fastforce intro:path_targetnode dest:DynPDG_ddep_edge_CFG_path)
            { fix V' assume "V' \<in> Use n"
              from `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` have "(V,[],[]) \<in> dependent_live_vars n''"
                by(fastforce elim:DynPDG_edge.cases dep_vars_Use 
                            simp:dyn_data_dependence_def)
              with `n'' -asx'\<rightarrow>\<^sub>d* n'` have "(V,[],[]@asx') \<in> dependent_live_vars n'"
                by(rule dependent_live_vars_dep_dependent_live_vars)
              have "(V',[],as) \<in> dependent_live_vars n'"
              proof(cases "asx' = []")
                case True
                with `n'' -asx'\<rightarrow>\<^sub>d* n'` have "n'' = n'"
                  by(fastforce intro:DynPDG_empty_path_eq_nodes)
                with `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` `V' \<in> Use n` True `as = a'#as'`
                  `a'#as' = asx@asx'`
                show ?thesis by(fastforce intro:dependent_live_vars_ddep_empty_fst)
              next
                case False
                with `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` `asx = ai#ais`
                  `(V,[],[]@asx') \<in> dependent_live_vars n'`
                have "(V,ais@[],ais@asx') \<in> dependent_live_vars n'"
                  by(fastforce intro:ddep_dependent_live_vars_keep_notempty)
                from `n'' -asx'\<rightarrow>\<^sub>d* n'` False have "last(targetnodes asx') = n'"
                  by -(rule path_targetnode,rule DynPDG_path_CFG_path)
                with `(V,ais@[],ais@asx') \<in> dependent_live_vars n'`
                  `V' \<in> Use n` `n -{V}asx\<rightarrow>\<^bsub>dd\<^esub> n''` `asx = ai#ais`
                  `sourcenode ai = n` `last(targetnodes asx) = n''` False
                have "(V',[],ai#ais@asx') \<in> dependent_live_vars n'"
                  by(fastforce intro:dep_vars_Cons_ddep simp:targetnodes_def)
                with `asx = ai#ais` `a'#as' = asx@asx'` `as = a'#as'`
                show ?thesis by simp
              qed
              with all have "state_val s V' = state_val s' V'" by blast }
            with `pred ex' s'` `valid_edge a'`
            show ?thesis by(fastforce elim:CFG_edge_Uses_pred_equal)
          qed
        qed
      qed simp
      with all' `preds esx (transfer ex s)` `es = ex#esx` `es' = ex'#esx'`
      show ?thesis by simp
    next
      case False
      then obtain V' xs' where "(V',xs',as') \<in> dependent_live_vars n'"
        and "state_val (transfer ex s) V' \<noteq> state_val (transfer ex' s') V'"
        by auto
      show ?thesis
      proof(cases "n -a'#as'\<rightarrow>\<^sub>d* n'")
        case True
        with `slice_path as = x#xs` `as = a'#as'` `last(targetnodes as) = n'` ex
        have [simp]:"ex = kind a'" by clarsimp
        with `x \<longrightarrow> y` ex ex' have [simp]:"ex' = ex" by(cases x) auto
        { fix V assume "V \<in> Use (sourcenode a')"
          hence "(V,[],[]) \<in> dependent_live_vars (sourcenode a')"
            by(rule dep_vars_Use)
          with `n -a'#as'\<rightarrow>\<^sub>d* n'` have "(V,[],[]@a'#as') \<in> dependent_live_vars n'"
            by(fastforce intro:dependent_live_vars_dep_dependent_live_vars)
          with all `as = a'#as'` have "state_val s V = state_val s' V"
            by fastforce }
        with `pred ex' s'` `valid_edge a'` have "pred ex s"
          by(fastforce intro:CFG_edge_Uses_pred_equal)
        show ?thesis
        proof(cases "V' \<in> Def n")
          case True
          with `state_val (transfer ex s) V' \<noteq> state_val (transfer ex' s') V'`
            `valid_edge a'` `pred ex' s'` `pred ex s`
            CFG_edge_transfer_uses_only_Use[of a' s s']
          obtain V'' where "V'' \<in> Use n"
            and "state_val s V'' \<noteq> state_val s' V''"
            by auto
          from True `(V',xs',as') \<in> dependent_live_vars n'`
            `targetnode a' -as'\<rightarrow>* n'` `last(targetnodes as) = n'` `as = a'#as'`
            `valid_edge a'` `n = sourcenode a'`[THEN sym]
          have "n -{V'}a'#xs'\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (a'#xs'))"
            by -(drule dependent_live_vars_dependent_edge,
              auto dest!: dependent_live_vars_dependent_edge 
                   dest:DynPDG_ddep_edge_CFG_path path_targetnode 
                   simp del:`n = sourcenode a'`)
          with `(V',xs',as') \<in> dependent_live_vars n'` `V'' \<in> Use n`
            `last(targetnodes as) = n'` `as = a'#as'`
          have "(V'',[],as) \<in> dependent_live_vars n'" 
            by(fastforce intro:dep_vars_Cons_ddep)
          with all have "state_val s V'' = state_val s' V''" by blast
          with `state_val s V'' \<noteq> state_val s' V''` have False by simp
          thus ?thesis by simp
        next
          case False
          with `valid_edge a'` `pred ex s`
          have "state_val (transfer (kind a') s) V' = state_val s V'"
            by(fastforce intro:CFG_edge_no_Def_equal)
          moreover
          from False `valid_edge a'` `pred ex' s'`
          have "state_val (transfer (kind a') s') V' = state_val s' V'"
            by(fastforce intro:CFG_edge_no_Def_equal)
          ultimately have "state_val s V' \<noteq> state_val s' V'"
            using `state_val (transfer ex s) V' \<noteq> state_val (transfer ex' s') V'`
            by simp
          from False have "\<not> n -{V'}a'#xs'\<rightarrow>\<^bsub>dd\<^esub> 
                           last(targetnodes (a'#xs'))"
            by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
          with `(V',xs',as') \<in> dependent_live_vars n'` `last(targetnodes as) = n'`
            `as = a'#as'`
          have "(V',a'#xs',a'#as') \<in> dependent_live_vars n'"
            by(fastforce intro:dep_vars_Cons_keep)
          with `as = a'#as'` all have "state_val s V' = state_val s' V'" by auto
          with `state_val s V' \<noteq> state_val s' V'` have False by simp
          thus ?thesis by simp
        qed
      next
        case False
        { assume "V' \<in> Def n"
          with `(V',xs',as') \<in> dependent_live_vars n'` `targetnode a' -as'\<rightarrow>* n'`
            `valid_edge a'`
          have "n -a'#as'\<rightarrow>\<^sub>d* n'"
            by -(drule dependent_live_vars_dependent_edge,
              auto dest:DynPDG_path_ddep DynPDG_path_Append)
          with False have "False" by simp }
        hence "V' \<notin> Def (sourcenode a')" by fastforce
        from False `slice_path as = x#xs` `as = a'#as'`
          `last(targetnodes as) = n'` `as' \<noteq> []`
        have "\<not> x" by(auto simp:targetnodes_def)
        with ex have cases:"ex = (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>)"
          by simp
        have "state_val s V' \<noteq> state_val s' V'"
        proof(cases y)
          case True
          with ex' have [simp]:"ex' = kind a'" by simp
          from `V' \<notin> Def (sourcenode a')` `valid_edge a'` `pred ex' s'`
          have states_eq:"state_val (transfer (kind a') s') V' = state_val s' V'"
            by(fastforce intro:CFG_edge_no_Def_equal)
          from cases have "state_val s V' = state_val (transfer ex s) V'"
            by(cases "kind a'") auto
          with states_eq
            `state_val (transfer ex s) V' \<noteq> state_val (transfer ex' s') V'`
          show ?thesis by simp
        next
          case False
          with ex' have "ex' = (case kind a' of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> (\<lambda>s. True)\<^sub>\<surd>)"
            by simp
          with cases have "state_val s V' = state_val (transfer ex s) V'"
            and "state_val s' V' = state_val (transfer ex' s') V'"
            by(cases "kind a'",auto)+
          with `state_val (transfer ex s) V' \<noteq> state_val (transfer ex' s') V'` 
          show ?thesis by simp
        qed
        from `V' \<notin> Def (sourcenode a')` 
        have "\<not> n -{V'}a'#xs'\<rightarrow>\<^bsub>dd\<^esub> last(targetnodes (a'#xs'))"
          by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
        with `(V',xs',as') \<in> dependent_live_vars n'` `last(targetnodes as) = n'`
          `as = a'#as'`
        have "(V',a'#xs',a'#as') \<in> dependent_live_vars n'"
          by(fastforce intro:dep_vars_Cons_keep)
        with `as = a'#as'` all have "state_val s V' = state_val s' V'" by auto
        with `state_val s V' \<noteq> state_val s' V'` have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed simp_all


theorem fundamental_property_of_path_slicing:
  assumes "n -as\<rightarrow>* n'" and "preds (kinds as) s"
  shows "(\<forall>V \<in> Use n'. state_val (transfers (slice_kinds as) s) V = 
                         state_val (transfers (kinds as) s) V)" 
  and "preds (slice_kinds as) s"
proof -
  have "length as = length (slice_path as)" by(simp add:slice_path_length)
  hence "slice_path as \<preceq>\<^sub>b replicate (length as) True"
    by(simp add:maximal_element)
  have "select_edge_kinds as (replicate (length as) True) = kinds as"
    by(rule select_edge_kinds_max_bv)
  with `n -as\<rightarrow>* n'` `slice_path as \<preceq>\<^sub>b replicate (length as) True`
    `preds (kinds as) s` 
  have "(\<forall>V\<in>Use n'. state_val (transfers (slice_kinds as) s) V =
       state_val (transfers (kinds as) s) V) \<and> preds (slice_kinds as) s"
    by -(rule slice_path_leqs_information_same_Uses,simp_all add:slice_kinds_def)
  thus "\<forall>V\<in>Use n'. state_val (transfers (slice_kinds as) s) V =
    state_val (transfers (kinds as) s) V" and "preds (slice_kinds as) s"
    by simp_all
qed

end


subsection {* The fundamental property of (dynamic) slicing related to the semantics *}

locale BackwardPathSlice_wf = 
  DynPDG sourcenode targetnode kind valid_edge Entry Def Use state_val Exit 
    dyn_control_dependence +
  CFG_semantics_wf sourcenode targetnode kind valid_edge Entry sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and dyn_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" 
    ("_ controls _ via _" [51, 0, 0] 1000)
  and Exit :: "'node" ("'('_Exit'_')") 
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80) 

begin

theorem fundamental_property_of_path_slicing_semantically:
  assumes "n \<triangleq> c" and "\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"
  obtains n' as where "n -as\<rightarrow>* n'" and "preds (slice_kinds as) s" 
  and "n' \<triangleq> c'" 
  and "\<forall>V \<in> Use n'. state_val (transfers (slice_kinds as) s) V = 
                     state_val s' V"
proof(atomize_elim)
  from `n \<triangleq> c` `\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>` obtain n' as where "n -as\<rightarrow>* n'"
    and "transfers (kinds as) s = s'"
    and "preds (kinds as) s"
    and "n' \<triangleq> c'"
    by(fastforce dest:fundamental_property)
  with `n -as\<rightarrow>* n'` `preds (kinds as) s` 
  have "\<forall>V \<in> Use n'. state_val (transfers (slice_kinds as) s) V =
    state_val (transfers (kinds as) s) V" and "preds (slice_kinds as) s"
    by -(rule fundamental_property_of_path_slicing,simp_all)+
  with `transfers (kinds as) s = s'` have "\<forall>V \<in> Use n'. 
    state_val (transfers (slice_kinds as) s) V =
    state_val s' V" by simp
  with `n -as\<rightarrow>* n'` `preds (slice_kinds as) s` `n' \<triangleq> c'`
  show "\<exists>as n'. n -as\<rightarrow>* n' \<and> preds (slice_kinds as) s \<and> n' \<triangleq> c' \<and>
       (\<forall>V\<in>Use n'. state_val (transfers (slice_kinds as) s) V = state_val s' V)"
    by blast
qed


end

end
