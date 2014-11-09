section {* CFG well-formedness *}

theory CFG_wf imports CFG begin

locale CFG_wf = CFG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname" +
  fixes Def::"'node \<Rightarrow> 'var set"
  fixes Use::"'node \<Rightarrow> 'var set"
  fixes ParamDefs::"'node \<Rightarrow> 'var list"
  fixes ParamUses::"'node \<Rightarrow> 'var set list"
  assumes Entry_empty:"Def (_Entry_) = {} \<and> Use (_Entry_) = {}"
  and ParamUses_call_source_length:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs\<rbrakk>
    \<Longrightarrow> length(ParamUses (sourcenode a)) = length ins"
  and distinct_ParamDefs:"valid_edge a \<Longrightarrow> distinct (ParamDefs (targetnode a))"
  and ParamDefs_return_target_length:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'; (p,ins,outs) \<in> set procs\<rbrakk>
    \<Longrightarrow> length(ParamDefs (targetnode a)) = length outs"
  and ParamDefs_in_Def:
    "\<lbrakk>valid_node n; V \<in> set (ParamDefs n)\<rbrakk> \<Longrightarrow> V \<in> Def n"
  and ins_in_Def:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs; V \<in> set ins\<rbrakk>
    \<Longrightarrow> V \<in> Def (targetnode a)"
  and call_source_Def_empty:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> Def (sourcenode a) = {}"
  and ParamUses_in_Use:
    "\<lbrakk>valid_node n; V \<in> Union (set (ParamUses n))\<rbrakk> \<Longrightarrow> V \<in> Use n"
  and outs_in_Use:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs; V \<in> set outs\<rbrakk> 
    \<Longrightarrow> V \<in> Use (sourcenode a)"
  and CFG_intra_edge_no_Def_equal:
    "\<lbrakk>valid_edge a; V \<notin> Def (sourcenode a); intra_kind (kind a); pred (kind a) s\<rbrakk>
    \<Longrightarrow> state_val (transfer (kind a) s) V = state_val s V"
  and CFG_intra_edge_transfer_uses_only_Use:
    "\<lbrakk>valid_edge a; \<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V;
      intra_kind (kind a); pred (kind a) s; pred (kind a) s'\<rbrakk>
    \<Longrightarrow> \<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s) V =
                                state_val (transfer (kind a) s') V"
  and CFG_edge_Uses_pred_equal:
    "\<lbrakk>valid_edge a; pred (kind a) s; snd (hd s) = snd (hd s');
      \<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V; length s = length s'\<rbrakk>
    \<Longrightarrow> pred (kind a) s'"
  and CFG_call_edge_length:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs\<rbrakk>
    \<Longrightarrow> length fs = length ins"
  and CFG_call_determ:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; valid_edge a'; kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs';
      sourcenode a = sourcenode a'; pred (kind a) s; pred (kind a') s\<rbrakk>
    \<Longrightarrow> a = a'"
  and CFG_call_edge_params:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; i < length ins; 
      (p,ins,outs) \<in> set procs; pred (kind a) s; pred (kind a) s';
      \<forall>V \<in> (ParamUses (sourcenode a))!i. state_val s V = state_val s' V\<rbrakk>
    \<Longrightarrow> (params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i"  
  and CFG_return_edge_fun:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'; (p,ins,outs) \<in> set procs\<rbrakk>
     \<Longrightarrow> f' vmap vmap' = vmap'(ParamDefs (targetnode a) [:=] map vmap outs)"
  and deterministic:"\<lbrakk>valid_edge a; valid_edge a'; sourcenode a = sourcenode a';
    targetnode a \<noteq> targetnode a'; intra_kind (kind a); intra_kind (kind a')\<rbrakk> 
    \<Longrightarrow> \<exists>Q Q'. kind a = (Q)\<^sub>\<surd> \<and> kind a' = (Q')\<^sub>\<surd> \<and> 
             (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"

begin


lemma CFG_equal_Use_equal_call:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge a'"
  and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'" and "sourcenode a = sourcenode a'"
  and "pred (kind a) s" and "pred (kind a') s'" 
  and "snd (hd s) = snd (hd s')" and "length s = length s'"
  and "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V"
  shows "a = a'"
proof -
  from `valid_edge a` `pred (kind a) s` `snd (hd s) = snd (hd s')`
    `\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V` `length s = length s'`
  have "pred (kind a) s'" by(rule CFG_edge_Uses_pred_equal)
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
    `sourcenode a = sourcenode a'` `pred (kind a') s'`
  show ?thesis by -(rule CFG_call_determ)
qed


lemma CFG_call_edge_param_in:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "i < length ins"
  and "(p,ins,outs) \<in> set procs" and "pred (kind a) s" and "pred (kind a) s'"
  and "\<forall>V \<in> (ParamUses (sourcenode a))!i. state_val s V = state_val s' V"
  shows "state_val (transfer (kind a) s) (ins!i) = 
         state_val (transfer (kind a) s') (ins!i)"
proof -
  from assms have params:"(params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i"
    by(rule CFG_call_edge_params)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
  have [simp]:"(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
    by(rule formal_in_THE)
  from `pred (kind a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from `pred (kind a) s'` obtain cf' cfs' where [simp]:"s' = cf'#cfs'"
    by(cases s') auto
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have eqs:"fst (hd (transfer (kind a) s)) = (empty(ins [:=] params fs (fst cf)))"
    "fst (hd (transfer (kind a) s')) = (empty(ins [:=] params fs (fst cf')))"
    by simp_all
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
  have "length fs = length ins" by(rule CFG_call_edge_length)
  from `(p,ins,outs) \<in> set procs` have "distinct ins" by(rule distinct_formal_ins)
  with `i < length ins` `length fs = length ins`
  have "(empty(ins [:=] params fs (fst cf))) (ins!i) = (params fs (fst cf))!i"
    "(empty(ins [:=] params fs (fst cf'))) (ins!i) = (params fs (fst cf'))!i"
    by(fastforce intro:fun_upds_nth)+
  with eqs `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` params
  show ?thesis by simp
qed


lemma CFG_call_edge_no_param:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "V \<notin> set ins"
  and "(p,ins,outs) \<in> set procs" and "pred (kind a) s"
  shows "state_val (transfer (kind a) s) V = None"
proof -
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
  have [simp]:"(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
    by(rule formal_in_THE)
  from `pred (kind a) s` obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
  from `V \<notin> set ins` have "(empty(ins [:=] params fs (fst cf))) V = None"
    by(auto dest:fun_upds_notin)
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?thesis by simp
qed



lemma CFG_return_edge_param_out:
  assumes "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "i < length outs"
  and "(p,ins,outs) \<in> set procs" and "state_val s (outs!i) = state_val s' (outs!i)"
  and "s = cf#cfx#cfs" and "s' = cf'#cfx'#cfs'"
  shows "state_val (transfer (kind a) s) ((ParamDefs (targetnode a))!i) =
         state_val (transfer (kind a) s') ((ParamDefs (targetnode a))!i)"
proof -
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs`
  have [simp]:"(THE outs. \<exists>ins. (p,ins,outs) \<in> set procs) = outs"
    by(rule formal_out_THE)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs` `s = cf#cfx#cfs`
  have transfer:"fst (hd (transfer (kind a) s)) = 
    (fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf) outs)"
    by(fastforce intro:CFG_return_edge_fun)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs` `s' = cf'#cfx'#cfs'`
  have transfer':"fst (hd (transfer (kind a) s')) = 
    (fst cfx')(ParamDefs (targetnode a) [:=] map (fst cf') outs)"
    by(fastforce intro:CFG_return_edge_fun)
  from `state_val s (outs!i) = state_val s' (outs!i)` `i < length outs`
    `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
  have "(fst cf) (outs!i) = (fst cf') (outs!i)" by simp
  from `valid_edge a` have "distinct (ParamDefs (targetnode a))"
    by(fastforce intro:distinct_ParamDefs)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs`
  have "length(ParamDefs (targetnode a)) = length outs"
    by(fastforce intro:ParamDefs_return_target_length)
  with `i < length outs` `distinct (ParamDefs (targetnode a))`
  have "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf) outs)
    ((ParamDefs (targetnode a))!i) = (map (fst cf) outs)!i" 
    and "(fst cfx')(ParamDefs (targetnode a) [:=] map (fst cf') outs)
             ((ParamDefs (targetnode a))!i) = (map (fst cf') outs)!i"
    by(fastforce intro:fun_upds_nth)+
  with transfer transfer' `(fst cf) (outs!i) = (fst cf') (outs!i)` `i < length outs`
  show ?thesis by simp
qed


lemma CFG_slp_no_Def_equal:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'" and "valid_edge a" and "a' \<in> get_return_edges a"
  and "V \<notin> set (ParamDefs (targetnode a'))" and "preds (kinds (a#as@[a'])) s"
  shows "state_val (transfers (kinds (a#as@[a'])) s) V = state_val s V"
proof -
  from `valid_edge a` `a' \<in> get_return_edges a` 
  obtain Q r p fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    by(fastforce dest!:only_call_get_return_edges)
  with `valid_edge a` `a' \<in> get_return_edges a` obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
    by(rule get_return_edges_valid)
  from `preds (kinds (a#as@[a'])) s` obtain cf cfs where [simp]:"s = cf#cfs"
    by(cases s,auto simp:kinds_def)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain ins outs 
    where "(p,ins,outs) \<in> set procs" by(fastforce dest!:callee_in_procs)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain cfx where "transfer (kind a) s = cfx#cf#cfs"
    by simp
  moreover
  from `n -as\<rightarrow>\<^bsub>sl\<^esub>* n'` obtain cfx' 
    where "transfers (kinds as) (cfx#cf#cfs) = cfx'#cf#cfs"
    by(fastforce elim:slp_callstack_length_equal)
  moreover
  from `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `valid_edge a'` `(p,ins,outs) \<in> set procs`
  have "fst (hd (transfer (kind a') (cfx'#cf#cfs))) = 
    (fst cf)(ParamDefs (targetnode a') [:=] map (fst cfx') outs)"
    by(simp,simp only:formal_out_THE,fastforce intro:CFG_return_edge_fun)
  ultimately have "fst (hd (transfers (kinds (a#as@[a'])) s)) = 
    (fst cf)(ParamDefs (targetnode a') [:=] map (fst cfx') outs)"
    by(simp add:kinds_def transfers_split)
  with `V \<notin> set (ParamDefs (targetnode a'))` show ?thesis
    by(simp add:fun_upds_notin)
qed



lemma [dest!]: "V \<in> Use (_Entry_) \<Longrightarrow> False"
by(simp add:Entry_empty)

lemma [dest!]: "V \<in> Def (_Entry_) \<Longrightarrow> False"
by(simp add:Entry_empty)


lemma CFG_intra_path_no_Def_equal:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" and "\<forall>n \<in> set (sourcenodes as). V \<notin> Def n"
  and "preds (kinds as) s"
  shows "state_val (transfers (kinds as) s) V = state_val s V"
proof -
  from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind (kind a)"
    by(simp_all add:intra_path_def)
  from this `\<forall>n \<in> set (sourcenodes as). V \<notin> Def n` `preds (kinds as) s`
  have "state_val (transfers (kinds as) s) V = state_val s V"
  proof(induct arbitrary:s rule:path.induct)
    case (empty_path n)
    thus ?case by(simp add:sourcenodes_def kinds_def)
  next
    case (Cons_path n'' as n' a n)
    note IH = `\<And>s. \<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); 
                    \<forall>n\<in>set (sourcenodes as). V \<notin> Def n; preds (kinds as) s\<rbrakk> 
      \<Longrightarrow> state_val (transfers (kinds as) s) V = state_val s V`
    from `preds (kinds (a#as)) s` have "pred (kind a) s"
      and "preds (kinds as) (transfer (kind a) s)" by(simp_all add:kinds_def)
    from `\<forall>n\<in>set (sourcenodes (a#as)). V \<notin> Def n`
    have noDef:"V \<notin> Def (sourcenode a)" 
      and all:"\<forall>n\<in>set (sourcenodes as). V \<notin> Def n"
      by(auto simp:sourcenodes_def)
    from `\<forall>a\<in>set (a#as). intra_kind (kind a)`
    have "intra_kind (kind a)" and all':"\<forall>a\<in>set as. intra_kind (kind a)"
      by auto
    from `valid_edge a` noDef `intra_kind (kind a)` `pred (kind a) s`
    have "state_val (transfer (kind a) s) V = state_val s V"
     by -(rule CFG_intra_edge_no_Def_equal)
    with IH[OF all' all `preds (kinds as) (transfer (kind a) s)`] show ?case
      by(simp add:kinds_def)
  qed
  thus ?thesis by blast
qed


lemma slpa_preds:
  "\<lbrakk>same_level_path_aux cs as; s = cfsx@cf#cfs; s' = cfsx@cf#cfs'; 
    length cfs = length cfs'; \<forall>a \<in> set as. valid_edge a; length cs = length cfsx; 
    preds (kinds as) s\<rbrakk>
  \<Longrightarrow> preds (kinds as) s'"
proof(induct arbitrary:s s' cf cfsx rule:slpa_induct)
  case (slpa_empty cs) thus ?case by(simp add:kinds_def)
next
  case (slpa_intra cs a as)
  note IH = `\<And>s s' cf cfsx. \<lbrakk>s = cfsx@cf#cfs; s' = cfsx@cf#cfs';
    length cfs = length cfs'; \<forall>a \<in> set as. valid_edge a; length cs = length cfsx; 
    preds (kinds as) s\<rbrakk> \<Longrightarrow> preds (kinds as) s'`
  from `\<forall>a\<in>set (a#as). valid_edge a` have "valid_edge a"
    and "\<forall>a \<in> set as. valid_edge a" by simp_all
  from `preds (kinds (a#as)) s` have "pred (kind a) s"
    and "preds (kinds as) (transfer (kind a) s)" by(simp_all add:kinds_def)
  show ?case
  proof(cases cfsx)
    case Nil
    with `length cs = length cfsx` have "length cs = length []" by simp
    from Nil `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'` `intra_kind (kind a)` 
    obtain cfx where "transfer (kind a) s = []@cfx#cfs"
      and "transfer (kind a) s' = []@cfx#cfs'"
      by(cases "kind a",auto simp:kinds_def intra_kind_def)
    from IH[OF this `length cfs = length cfs'` `\<forall>a \<in> set as. valid_edge a`
      `length cs = length []` `preds (kinds as) (transfer (kind a) s)`]
    have "preds (kinds as) (transfer (kind a) s')" .
    moreover
    from Nil `valid_edge a` `pred (kind a) s` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
      `length cfs = length cfs'`
    have "pred (kind a) s'" by(fastforce intro:CFG_edge_Uses_pred_equal)
    ultimately show ?thesis by(simp add:kinds_def)
  next
    case (Cons x xs)
    with `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'` `intra_kind (kind a)`
    obtain cfx where "transfer (kind a) s = (cfx#xs)@cf#cfs"
      and "transfer (kind a) s' = (cfx#xs)@cf#cfs'"
      by(cases "kind a",auto simp:kinds_def intra_kind_def)
    from IH[OF this `length cfs = length cfs'` `\<forall>a \<in> set as. valid_edge a` _ 
      `preds (kinds as) (transfer (kind a) s)`] `length cs = length cfsx` Cons
    have "preds (kinds as) (transfer (kind a) s')" by simp
    moreover
    from Cons `valid_edge a` `pred (kind a) s` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
      `length cfs = length cfs'` 
    have "pred (kind a) s'" by(fastforce intro:CFG_edge_Uses_pred_equal)
    ultimately show ?thesis by(simp add:kinds_def)
  qed
next
  case (slpa_Call cs a as Q r p fs)
  note IH = `\<And>s s' cf cfsx. \<lbrakk>s = cfsx@cf#cfs; s' = cfsx@cf#cfs';
    length cfs = length cfs'; \<forall>a \<in> set as. valid_edge a; length (a#cs) = length cfsx;
    preds (kinds as) s\<rbrakk> \<Longrightarrow> preds (kinds as) s'`
  from `\<forall>a\<in>set (a#as). valid_edge a` have "valid_edge a"
    and "\<forall>a \<in> set as. valid_edge a" by simp_all
  from `preds (kinds (a#as)) s` have "pred (kind a) s"
    and "preds (kinds as) (transfer (kind a) s)" by(simp_all add:kinds_def)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'` obtain cfx
    where "transfer (kind a) s = (cfx#cfsx)@cf#cfs"
    and "transfer (kind a) s' = (cfx#cfsx)@cf#cfs'" by(cases cfsx) auto
  from IH[OF this `length cfs = length cfs'` `\<forall>a \<in> set as. valid_edge a` _ 
    `preds (kinds as) (transfer (kind a) s)`] `length cs = length cfsx`
  have "preds (kinds as) (transfer (kind a) s')" by simp
  moreover
  from `valid_edge a` `pred (kind a) s` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
    `length cfs = length cfs'` have "pred (kind a) s'" 
    by(cases cfsx)(auto intro:CFG_edge_Uses_pred_equal)
  ultimately show ?case by(simp add:kinds_def)
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = `\<And>s s' cf cfsx. \<lbrakk>s = cfsx@cf#cfs; s' = cfsx@cf#cfs';
    length cfs = length cfs'; \<forall>a \<in> set as. valid_edge a; length cs' = length cfsx; 
    preds (kinds as) s\<rbrakk> \<Longrightarrow> preds (kinds as) s'`
  from `\<forall>a\<in>set (a#as). valid_edge a` have "valid_edge a"
    and "\<forall>a \<in> set as. valid_edge a" by simp_all
  from `preds (kinds (a#as)) s` have "pred (kind a) s"
    and "preds (kinds as) (transfer (kind a) s)" by(simp_all add:kinds_def)
  show ?case
  proof(cases cs')
    case Nil
    with `cs = c'#cs'` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
      `length cs = length cfsx` 
    obtain cf' where "s = cf'#cf#cfs" and "s' = cf'#cf#cfs'" by(cases cfsx) auto
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain cf'' where "transfer (kind a) s = []@cf''#cfs"
      and "transfer (kind a) s' = []@cf''#cfs'" by auto
    from IH[OF this `length cfs = length cfs'` `\<forall>a \<in> set as. valid_edge a` _ 
      `preds (kinds as) (transfer (kind a) s)`] Nil
    have "preds (kinds as) (transfer (kind a) s')" by simp
    moreover
    from `valid_edge a` `pred (kind a) s` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
      `length cfs = length cfs'`  have "pred (kind a) s'" 
      by(cases cfsx)(auto intro:CFG_edge_Uses_pred_equal)
    ultimately show ?thesis by(simp add:kinds_def)
  next
    case (Cons cx csx)
    with `cs = c'#cs'` `length cs = length cfsx` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
    obtain x x' xs where "s = (x#x'#xs)@cf#cfs" and "s' = (x#x'#xs)@cf#cfs'"
      and "length xs = length csx"
      by(cases cfsx,auto,case_tac list,fastforce+)
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain cf' where "transfer (kind a) s = (cf'#xs)@cf#cfs"
      and "transfer (kind a) s' = (cf'#xs)@cf#cfs'"
      by fastforce
    from IH[OF this `length cfs = length cfs'` `\<forall>a \<in> set as. valid_edge a` _ 
      `preds (kinds as) (transfer (kind a) s)`] Cons `length xs = length csx`
    have "preds (kinds as) (transfer (kind a) s')" by simp
    moreover
    from `valid_edge a` `pred (kind a) s` `s = cfsx@cf#cfs` `s' = cfsx@cf#cfs'`
      `length cfs = length cfs'`  have "pred (kind a) s'" 
      by(cases cfsx)(auto intro:CFG_edge_Uses_pred_equal)
    ultimately show ?thesis by(simp add:kinds_def)
  qed
qed


lemma slp_preds:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'" and "preds (kinds as) (cf#cfs)" 
  and "length cfs = length cfs'"
  shows "preds (kinds as) (cf#cfs')"
proof -
  from `n -as\<rightarrow>\<^bsub>sl\<^esub>* n'` have "n -as\<rightarrow>* n'" and "same_level_path_aux [] as"
    by(simp_all add:slp_def same_level_path_def)
  from `n -as\<rightarrow>* n'` have "\<forall>a \<in> set as. valid_edge a" by(rule path_valid_edges)
  with `same_level_path_aux [] as` `preds (kinds as) (cf#cfs)` 
    `length cfs = length cfs'`
  show ?thesis by(fastforce elim!:slpa_preds)
qed
end


end
