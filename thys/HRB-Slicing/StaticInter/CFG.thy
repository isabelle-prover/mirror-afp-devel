section {* CFG *}

theory CFG imports BasicDefs begin

subsection {* The abstract CFG *}

subsubsection {* Locale fixes and assumptions *}

locale CFG =
  fixes sourcenode :: "'edge \<Rightarrow> 'node"
  fixes targetnode :: "'edge \<Rightarrow> 'node"
  fixes kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind"
  fixes valid_edge :: "'edge \<Rightarrow> bool"
  fixes Entry::"'node" ("'('_Entry'_')")
  fixes get_proc::"'node \<Rightarrow> 'pname"
  fixes get_return_edges::"'edge \<Rightarrow> 'edge set"
  fixes procs::"('pname \<times> 'var list \<times> 'var list) list"
  fixes Main::"'pname"
  assumes Entry_target [dest]: "\<lbrakk>valid_edge a; targetnode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and get_proc_Entry:"get_proc (_Entry_) = Main"
  and Entry_no_call_source:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; sourcenode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and edge_det: 
    "\<lbrakk>valid_edge a; valid_edge a'; sourcenode a = sourcenode a'; 
      targetnode a = targetnode a'\<rbrakk> \<Longrightarrow> a = a'" 
  and Main_no_call_target:"\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>f\<rbrakk> \<Longrightarrow> False" 
  and Main_no_return_source:"\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>Main\<^esub>f'\<rbrakk> \<Longrightarrow> False" 
  and callee_in_procs: 
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> \<exists>ins outs. (p,ins,outs) \<in> set procs" 
  and get_proc_intra:"\<lbrakk>valid_edge a; intra_kind(kind a)\<rbrakk>
    \<Longrightarrow> get_proc (sourcenode a) = get_proc (targetnode a)" 
  and get_proc_call:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> get_proc (targetnode a) = p"
  and get_proc_return:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> \<Longrightarrow> get_proc (sourcenode a) = p"
  and call_edges_only:"\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
    \<Longrightarrow> \<forall>a'. valid_edge a' \<and> targetnode a' = targetnode a \<longrightarrow> 
            (\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
  and return_edges_only:"\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> 
    \<Longrightarrow> \<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<longrightarrow> 
            (\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)" 
  and get_return_edge_call:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> get_return_edges a \<noteq> {}" 
  and get_return_edges_valid:
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk> \<Longrightarrow> valid_edge a'" 
  and only_call_get_return_edges:
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk> \<Longrightarrow> \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
  and call_return_edges:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a\<rbrakk> 
    \<Longrightarrow> \<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" 
  and return_needs_call: "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk>
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges a'"
  and intra_proc_additional_edge: 
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk>
    \<Longrightarrow> \<exists>a''. valid_edge a'' \<and> sourcenode a'' = targetnode a \<and> 
              targetnode a'' = sourcenode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
  and call_return_node_edge: 
  "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk>
    \<Longrightarrow> \<exists>a''. valid_edge a'' \<and> sourcenode a'' = sourcenode a \<and> 
             targetnode a'' = targetnode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
  and call_only_one_intra_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> intra_kind(kind a')"
 and return_only_one_intra_edge:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> 
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> targetnode a' = targetnode a \<and> intra_kind(kind a')"
  and same_proc_call_unique_target:
    "\<lbrakk>valid_edge a; valid_edge a'; kind a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1;  kind a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2\<rbrakk>
    \<Longrightarrow> targetnode a = targetnode a'"
  and unique_callers:"distinct_fst procs" 
  and distinct_formal_ins:"(p,ins,outs) \<in> set procs \<Longrightarrow> distinct ins"
  and distinct_formal_outs:"(p,ins,outs) \<in> set procs \<Longrightarrow> distinct outs"

begin


lemma get_proc_get_return_edge:
  assumes "valid_edge a" and "a' \<in> get_return_edges a"
  shows "get_proc (sourcenode a) = get_proc (targetnode a')"
proof -
  from assms obtain ax where "valid_edge ax" and "sourcenode a = sourcenode ax"
    and "targetnode a' = targetnode ax" and "intra_kind(kind ax)"
    by(auto dest:call_return_node_edge simp:intra_kind_def)
  thus ?thesis by(fastforce intro:get_proc_intra)
qed


lemma call_intra_edge_False:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge a'" 
  and "sourcenode a = sourcenode a'" and "intra_kind(kind a')"
  shows "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
proof -
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain ax where "ax \<in> get_return_edges a"
    by(fastforce dest:get_return_edge_call)
  with `valid_edge a` obtain a'' where "valid_edge a''" 
    and "sourcenode a'' = sourcenode a" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>` have "intra_kind(kind a'')" 
    by(simp add:intra_kind_def)
  with assms `valid_edge a''` `sourcenode a'' = sourcenode a` 
    `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>`
  show ?thesis by(fastforce dest:call_only_one_intra_edge)
qed


lemma formal_in_THE: 
  "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
by(fastforce dest:distinct_fst_isin_same_fst intro:unique_callers)

lemma formal_out_THE: 
  "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE outs. \<exists>ins. (p,ins,outs) \<in> set procs) = outs"
by(fastforce dest:distinct_fst_isin_same_fst intro:unique_callers)


subsubsection {* Transfer and predicate functions *}

fun params :: "(('var \<rightharpoonup> 'val) \<rightharpoonup> 'val) list \<Rightarrow> ('var \<rightharpoonup> 'val) \<Rightarrow> 'val option list"
where "params [] cf = []"
  | "params (f#fs) cf = (f cf)#params fs cf"


lemma params_nth: 
  "i < length fs \<Longrightarrow> (params fs cf)!i = (fs!i) cf"
by(induct fs arbitrary:i,auto,case_tac i,auto)


lemma [simp]:"length (params fs cf) = length fs"
  by(induct fs) auto


fun transfer :: "('var,'val,'ret,'pname) edge_kind \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list"
where "transfer (\<Up>f) (cf#cfs)    = (f (fst cf),snd cf)#cfs"
  | "transfer (Q)\<^sub>\<surd> (cf#cfs)      = (cf#cfs)"
  | "transfer (Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) (cf#cfs) = 
       (let ins = THE ins. \<exists>outs. (p,ins,outs) \<in> set procs in
                            (empty(ins [:=] params fs (fst cf)),r)#cf#cfs)"
  | "transfer (Q\<hookleftarrow>\<^bsub>p\<^esub>f )(cf#cfs)    = (case cfs of [] \<Rightarrow> []
                                 | cf'#cfs' \<Rightarrow> (f (fst cf) (fst cf'),snd cf')#cfs')"
  | "transfer et [] = []"

fun transfers :: "('var,'val,'ret,'pname) edge_kind list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow>
                  (('var \<rightharpoonup> 'val) \<times> 'ret) list"
where "transfers [] s   = s"
  | "transfers (et#ets) s = transfers ets (transfer et s)"


fun pred :: "('var,'val,'ret,'pname) edge_kind \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
where "pred (\<Up>f) (cf#cfs) = True"
  | "pred (Q)\<^sub>\<surd> (cf#cfs)   = Q (fst cf)"
  | "pred (Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) (cf#cfs) = Q (fst cf,r)"
  | "pred (Q\<hookleftarrow>\<^bsub>p\<^esub>f) (cf#cfs) = (Q cf \<and> cfs \<noteq> [])"
  | "pred et [] = False"

fun preds :: "('var,'val,'ret,'pname) edge_kind list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
where "preds [] s   = True"
  | "preds (et#ets) s = (pred et s \<and> preds ets (transfer et s))"


lemma transfers_split:
  "(transfers (ets@ets') s) = (transfers ets' (transfers ets s))"
by(induct ets arbitrary:s) auto

lemma preds_split:
  "(preds (ets@ets') s) = (preds ets s \<and> preds ets' (transfers ets s))"
by(induct ets arbitrary:s) auto


abbreviation state_val :: "(('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'var \<rightharpoonup> 'val"
  where "state_val s V \<equiv> (fst (hd s)) V"


subsubsection {* @{text "valid_node"} *}

definition valid_node :: "'node \<Rightarrow> bool"
  where "valid_node n \<equiv> 
  (\<exists>a. valid_edge a \<and> (n = sourcenode a \<or> n = targetnode a))"

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (sourcenode a)"
  by(fastforce simp:valid_node_def)

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (targetnode a)"
  by(fastforce simp:valid_node_def)



subsection {* CFG paths *}

inductive path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>* _" [51,0,0] 80)
where 
  empty_path:"valid_node n \<Longrightarrow> n -[]\<rightarrow>* n"

  | Cons_path:
  "\<lbrakk>n'' -as\<rightarrow>* n'; valid_edge a; sourcenode a = n; targetnode a = n''\<rbrakk>
    \<Longrightarrow> n -a#as\<rightarrow>* n'"


lemma path_valid_node:
  assumes "n -as\<rightarrow>* n'" shows "valid_node n" and "valid_node n'"
  using `n -as\<rightarrow>* n'`
  by(induct rule:path.induct,auto)

lemma empty_path_nodes [dest]:"n -[]\<rightarrow>* n' \<Longrightarrow> n = n'"
  by(fastforce elim:path.cases)

lemma path_valid_edges:"n -as\<rightarrow>* n' \<Longrightarrow> \<forall>a \<in> set as. valid_edge a"
by(induct rule:path.induct) auto


lemma path_edge:"valid_edge a \<Longrightarrow> sourcenode a -[a]\<rightarrow>* targetnode a"
  by(fastforce intro:Cons_path empty_path)


lemma path_Append:"\<lbrakk>n -as\<rightarrow>* n''; n'' -as'\<rightarrow>* n'\<rbrakk> 
  \<Longrightarrow> n -as@as'\<rightarrow>* n'"
by(induct rule:path.induct,auto intro:Cons_path)


lemma path_split:
  assumes "n -as@a#as'\<rightarrow>* n'"
  shows "n -as\<rightarrow>* sourcenode a" and "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
  using `n -as@a#as'\<rightarrow>* n'`
proof(induct as arbitrary:n)
  case Nil case 1
  thus ?case by(fastforce elim:path.cases intro:empty_path)
next
  case Nil case 2
  thus ?case by(fastforce elim:path.cases intro:path_edge)
next
  case Nil case 3
  thus ?case by(fastforce elim:path.cases)
next
  case (Cons ax asx) 
  note IH1 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> n -asx\<rightarrow>* sourcenode a`
  note IH2 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> valid_edge a`
  note IH3 = `\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> targetnode a -as'\<rightarrow>* n'`
  { case 1 
    hence "sourcenode ax = n" and "targetnode ax -asx@a#as'\<rightarrow>* n'" and "valid_edge ax"
      by(auto elim:path.cases)
    from IH1[OF ` targetnode ax -asx@a#as'\<rightarrow>* n'`] 
    have "targetnode ax -asx\<rightarrow>* sourcenode a" .
    with `sourcenode ax = n` `valid_edge ax` show ?case by(fastforce intro:Cons_path)
  next
    case 2 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH2[OF this] show ?case .
  next
    case 3 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH3[OF this] show ?case .
  }
qed


lemma path_split_Cons:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = a'#as'" and "n = sourcenode a'"
  and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
proof(atomize_elim)
  from `as \<noteq> []` obtain a' as' where "as = a'#as'" by(cases as) auto
  with `n -as\<rightarrow>* n'` have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "n -[]\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(rule path_split)+
  from `n -[]\<rightarrow>* sourcenode a'` have "n = sourcenode a'" by fast
  with `as = a'#as'` `valid_edge a'` `targetnode a' -as'\<rightarrow>* n'`
  show "\<exists>a' as'. as = a'#as' \<and> n = sourcenode a' \<and> valid_edge a' \<and> 
                 targetnode a' -as'\<rightarrow>* n'"
    by fastforce
qed


lemma path_split_snoc:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof(atomize_elim)
  from `as \<noteq> []` obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  with `n -as\<rightarrow>* n'` have "n -as'@a'#[]\<rightarrow>* n'" by simp
  hence "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -[]\<rightarrow>* n'"
    by(rule path_split)+
  from `targetnode a' -[]\<rightarrow>* n'` have "n' = targetnode a'" by fast
  with `as = as'@[a']` `valid_edge a'` `n -as'\<rightarrow>* sourcenode a'`
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>* sourcenode a' \<and> valid_edge a' \<and> 
                 n' = targetnode a'"
    by fastforce
qed


lemma path_split_second:
  assumes "n -as@a#as'\<rightarrow>* n'" shows "sourcenode a -a#as'\<rightarrow>* n'"
proof -
  from `n -as@a#as'\<rightarrow>* n'` have "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
    by(auto intro:path_split)
  thus ?thesis by(fastforce intro:Cons_path)
qed


lemma path_Entry_Cons:
  assumes "(_Entry_) -as\<rightarrow>* n'" and "n' \<noteq> (_Entry_)"
  obtains n a where "sourcenode a = (_Entry_)" and "targetnode a = n"
  and "n -tl as\<rightarrow>* n'" and "valid_edge a" and "a = hd as"
proof(atomize_elim)
  from `(_Entry_) -as\<rightarrow>* n'` `n' \<noteq> (_Entry_)` have "as \<noteq> []"
    by(cases as,auto elim:path.cases)
  with `(_Entry_) -as\<rightarrow>* n'` obtain a' as' where "as = a'#as'" 
    and "(_Entry_) = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(erule path_split_Cons)
  thus "\<exists>a n. sourcenode a = (_Entry_) \<and> targetnode a = n \<and> n -tl as\<rightarrow>* n' \<and> 
              valid_edge a \<and> a = hd as"
  by fastforce
qed


lemma path_det:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''"
proof(induct as arbitrary:n)
  case Nil thus ?case by(auto elim:path.cases)
next
  case (Cons a' as')
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; n -as'\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''`
  from `n -a'#as'\<rightarrow>* n'` have "targetnode a' -as'\<rightarrow>* n'" 
    by(fastforce elim:path_split_Cons)
  from `n -a'#as'\<rightarrow>* n''` have "targetnode a' -as'\<rightarrow>* n''" 
    by(fastforce elim:path_split_Cons)
  from IH[OF `targetnode a' -as'\<rightarrow>* n'` this] show ?thesis .
qed


definition
  sourcenodes :: "'edge list \<Rightarrow> 'node list"
  where "sourcenodes xs \<equiv> map sourcenode xs"

definition
  kinds :: "'edge list \<Rightarrow> ('var,'val,'ret,'pname) edge_kind list"
  where "kinds xs \<equiv> map kind xs"

definition
  targetnodes :: "'edge list \<Rightarrow> 'node list"
  where "targetnodes xs \<equiv> map targetnode xs"


lemma path_sourcenode:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> hd (sourcenodes as) = n"
by(fastforce elim:path_split_Cons simp:sourcenodes_def)



lemma path_targetnode:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> last (targetnodes as) = n'"
by(fastforce elim:path_split_snoc simp:targetnodes_def)



lemma sourcenodes_is_n_Cons_butlast_targetnodes:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
  sourcenodes as = n#(butlast (targetnodes as))"
proof(induct as arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons a' as')
  note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
            \<Longrightarrow> sourcenodes as' = n#(butlast (targetnodes as'))`
  from `n -a'#as'\<rightarrow>* n'` have "n = sourcenode a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(auto elim:path_split_Cons)
  show ?case
  proof(cases "as' = []")
    case True
    with `targetnode a' -as'\<rightarrow>* n'` have "targetnode a' = n'" by fast
    with True `n = sourcenode a'` show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF `targetnode a' -as'\<rightarrow>* n'` this] 
    have "sourcenodes as' = targetnode a' # butlast (targetnodes as')" .
    with `n = sourcenode a'` False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed



lemma targetnodes_is_tl_sourcenodes_App_n':
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
    targetnodes as = (tl (sourcenodes as))@[n']"
proof(induct as arbitrary:n' rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>n'. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
    \<Longrightarrow> targetnodes as' = tl (sourcenodes as') @ [n']`
  from `n -as'@[a']\<rightarrow>* n'` have "n -as'\<rightarrow>* sourcenode a'" and "n' = targetnode a'"
    by(auto elim:path_split_snoc)
  show ?case
  proof(cases "as' = []")
    case True
    with `n -as'\<rightarrow>* sourcenode a'` have "n = sourcenode a'" by fast
    with True `n' = targetnode a'` show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF `n -as'\<rightarrow>* sourcenode a'` this]
    have "targetnodes as' = tl (sourcenodes as')@[sourcenode a']" .
    with `n' = targetnode a'` False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed


subsubsection {* Intraprocedural paths *}

definition intra_path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ -_\<rightarrow>\<^sub>\<iota>* _" [51,0,0] 80)
where "n -as\<rightarrow>\<^sub>\<iota>* n' \<equiv> n -as\<rightarrow>* n' \<and> (\<forall>a \<in> set as. intra_kind(kind a))"

lemma intra_path_get_procs:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" shows "get_proc n = get_proc n'"
proof -
  from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
    by(simp_all add:intra_path_def)
  thus ?thesis
  proof(induct as arbitrary:n)
    case Nil thus ?case by fastforce
  next
    case (Cons a' as')
    note IH = `\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; \<forall>a\<in>set as'. intra_kind (kind a)\<rbrakk>
      \<Longrightarrow> get_proc n = get_proc n'`
    from `\<forall>a\<in>set (a'#as'). intra_kind (kind a)`
    have "intra_kind(kind a')" and "\<forall>a\<in>set as'. intra_kind (kind a)" by simp_all
    from `n -a'#as'\<rightarrow>* n'` have "sourcenode a' = n" and "valid_edge a'"
      and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH[OF `targetnode a' -as'\<rightarrow>* n'` `\<forall>a\<in>set as'. intra_kind (kind a)`]
    have "get_proc (targetnode a') = get_proc n'" .
    from `valid_edge a'` `intra_kind(kind a')` 
    have "get_proc (sourcenode a') = get_proc (targetnode a')"
      by(rule get_proc_intra)
    with `sourcenode a' = n` `get_proc (targetnode a') = get_proc n'`
    show ?case by simp
  qed
qed


lemma intra_path_Append:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<iota>* n''; n'' -as'\<rightarrow>\<^sub>\<iota>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<iota>* n'"
by(fastforce intro:path_Append simp:intra_path_def)


lemma get_proc_get_return_edges: 
  assumes "valid_edge a" and "a' \<in> get_return_edges a"
  shows "get_proc(targetnode a) = get_proc(sourcenode a')"
proof -
  from `valid_edge a` `a' \<in> get_return_edges a`
  obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
    and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:intra_proc_additional_edge)
  from `valid_edge a''` `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>`
  have "get_proc(sourcenode a'') = get_proc(targetnode a'')"
    by(fastforce intro:get_proc_intra simp:intra_kind_def)
  with `sourcenode a'' = targetnode a` `targetnode a'' = sourcenode a'`
  show ?thesis by simp
qed


subsubsection {* Valid paths *}

declare conj_cong[fundef_cong]

fun valid_path_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "valid_path_aux cs [] \<longleftrightarrow> True"
  | "valid_path_aux cs (a#as) \<longleftrightarrow> 
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> valid_path_aux (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> valid_path_aux [] as
                                     | c'#cs' \<Rightarrow> a \<in> get_return_edges c' \<and>
                                                 valid_path_aux cs' as
                       |    _ \<Rightarrow> valid_path_aux cs as)"


lemma vpa_induct [consumes 1,case_names vpa_empty vpa_intra vpa_Call vpa_ReturnEmpty
  vpa_ReturnCons]:
  assumes major: "valid_path_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); valid_path_aux cs as; P cs as\<rbrakk> \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; valid_path_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = []; valid_path_aux [] as; P [] as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f c' cs' . \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = c'#cs'; valid_path_aux cs' as;
                              a \<in> get_return_edges c'; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (a#as)"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma valid_path_aux_intra_path:
  "\<forall>a \<in> set as. intra_kind(kind a) \<Longrightarrow> valid_path_aux cs as"
by(induct as,auto simp:intra_kind_def)


lemma valid_path_aux_callstack_prefix:
  "valid_path_aux (cs@cs') as \<Longrightarrow> valid_path_aux cs as"
proof(induct "cs@cs'" as arbitrary:cs cs' rule:vpa_induct)
  case vpa_empty thus ?case by simp
next
  case (vpa_intra a as)
  hence "valid_path_aux cs as" by simp
  with `intra_kind (kind a)` show ?case by(cases "kind a",auto simp:intra_kind_def)
next
  case (vpa_Call a as Q r p fs cs'' cs')
  note IH = `\<And>xs ys. a#cs''@cs' = xs@ys \<Longrightarrow> valid_path_aux xs as`
  have "a#cs''@cs' = (a#cs'')@cs'" by simp
  from IH[OF this] have "valid_path_aux (a#cs'') as" .
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?case by simp
next
  case (vpa_ReturnEmpty a as Q p f cs'' cs')
  hence "valid_path_aux cs'' as" by simp
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs''@cs' = []` show ?case by simp
next
  case (vpa_ReturnCons a as Q p f c' cs' csx csx')
  note IH = `\<And>xs ys. cs' = xs@ys \<Longrightarrow> valid_path_aux xs as`
  from `csx@csx' = c'#cs'` 
  have "csx = [] \<and> csx' = c'#cs' \<or> (\<exists>zs. csx = c'#zs \<and> zs@csx' = cs')"
    by(simp add:append_eq_Cons_conv)
  thus ?case
  proof
    assume "csx = [] \<and> csx' = c'#cs'"
    hence "csx = []" and "csx' = c'#cs'" by simp_all
    from `csx' = c'#cs'` have "cs' = []@tl csx'" by simp
    from IH[OF this] have "valid_path_aux [] as" .
    with `csx = []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show ?thesis by simp
  next
    assume "\<exists>zs. csx = c'#zs \<and> zs@csx' = cs'"
    then obtain zs where "csx = c'#zs" and "cs' = zs@csx'" by auto
    from IH[OF `cs' = zs@csx'`] have "valid_path_aux zs as" .
    with `csx = c'#zs` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `a \<in> get_return_edges c'` 
    show ?thesis by simp
  qed
qed


fun upd_cs :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "upd_cs cs [] = cs"
  | "upd_cs cs (a#as) =
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> upd_cs (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> upd_cs cs as
                                      | c'#cs' \<Rightarrow> upd_cs cs' as
                       |    _ \<Rightarrow> upd_cs cs as)"


lemma upd_cs_empty [dest]:
  "upd_cs cs [] = [] \<Longrightarrow> cs = []"
by(cases cs) auto


lemma upd_cs_intra_path:
  "\<forall>a \<in> set as. intra_kind(kind a) \<Longrightarrow> upd_cs cs as = cs"
by(induct as,auto simp:intra_kind_def)


lemma upd_cs_Append:
  "\<lbrakk>upd_cs cs as = cs'; upd_cs cs' as' = cs''\<rbrakk> \<Longrightarrow> upd_cs cs (as@as') = cs''"
by(induct as arbitrary:cs,auto split:edge_kind.split list.split)


lemma upd_cs_empty_split:
  assumes "upd_cs cs as = []" and "cs \<noteq> []" and "as \<noteq> []"
  obtains xs ys where "as = xs@ys" and "xs \<noteq> []" and "upd_cs cs xs = []"
  and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
  and "upd_cs [] ys = []"
proof(atomize_elim)
  from `upd_cs cs as = []` `cs \<noteq> []` `as \<noteq> []`
  show "\<exists>xs ys. as = xs@ys \<and> xs \<noteq> [] \<and> upd_cs cs xs = [] \<and> 
             (\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []) \<and> 
             upd_cs [] ys = []"
  proof(induct as arbitrary:cs)
    case Nil thus ?case by simp
  next
    case (Cons a' as')
    note IH = `\<And>cs. \<lbrakk>upd_cs cs as' = []; cs \<noteq> []; as' \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>xs ys. as' = xs@ys \<and> xs \<noteq> [] \<and> upd_cs cs xs = [] \<and>
                 (\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []) \<and> 
                 upd_cs [] ys = []`
    show ?case
    proof(cases "kind a'" rule:edge_kind_cases)
      case Intra
      with `upd_cs cs (a'#as') = []` have "upd_cs cs as' = []"
        by(fastforce simp:intra_kind_def)
      with `cs \<noteq> []` have "as' \<noteq> []" by fastforce
      from IH[OF `upd_cs cs as' = []` `cs \<noteq> []` this] obtain xs ys where "as' = xs@ys"
        and "xs \<noteq> []" and "upd_cs cs xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []" by blast
      from `upd_cs cs xs = []` Intra have "upd_cs cs (a'#xs) = []"
        by(fastforce simp:intra_kind_def)
      from `\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []` `xs \<noteq> []` Intra
      have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
        apply auto
        apply(case_tac xs') apply(auto simp:intra_kind_def)
        by(erule_tac x="[]" in allE,fastforce)+
      with `as' = xs@ys` `upd_cs cs (a'#xs) = []` `upd_cs [] ys = []`
      show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
    next
      case (Call Q p f)
      with `upd_cs cs (a'#as') = []` have "upd_cs (a'#cs) as' = []" by simp
      with `cs \<noteq> []` have "as' \<noteq> []" by fastforce
      from IH[OF `upd_cs (a'#cs) as' = []` _ this] obtain xs ys where "as' = xs@ys"
        and "xs \<noteq> []" and "upd_cs (a'#cs) xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs (a'#cs) xs' \<noteq> []" by blast
      from `upd_cs (a'#cs) xs = []` Call have "upd_cs cs (a'#xs) = []" by simp
      from `\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs (a'#cs) xs' \<noteq> []` 
        `xs \<noteq> []` `cs \<noteq> []` Call
      have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
        by auto(case_tac xs',auto)
      with `as' = xs@ys` `upd_cs cs (a'#xs) = []` `upd_cs [] ys = []`
      show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
    next
      case (Return Q p f)
      with `upd_cs cs (a'#as') = []` `cs \<noteq> []` obtain c' cs' where "cs = c'#cs'"
        and "upd_cs cs' as' = []" by(cases cs) auto
      show ?thesis
      proof(cases "cs' = []")
        case True
        with `cs = c'#cs'` `upd_cs cs' as' = []` Return show ?thesis
          apply(rule_tac x="[a']" in exI) apply clarsimp
          by(case_tac xs') auto
      next
        case False
        with `upd_cs cs' as' = []` have "as' \<noteq> []" by fastforce
        from IH[OF `upd_cs cs' as' = []` False this] obtain xs ys where "as' = xs@ys"
          and "xs \<noteq> []" and "upd_cs cs' xs = []" and "upd_cs [] ys = []"
          and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs' xs' \<noteq> []" by blast
        from `upd_cs cs' xs = []` `cs = c'#cs'` Return have "upd_cs cs (a'#xs) = []"
          by simp
        from `\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs' xs' \<noteq> []`
          `xs \<noteq> []` `cs = c'#cs'` Return
        have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
          by auto(case_tac xs',auto)
        with `as' = xs@ys` `upd_cs cs (a'#xs) = []` `upd_cs [] ys = []`
        show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
      qed
    qed
  qed
qed


lemma upd_cs_snoc_Return_Cons:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "upd_cs cs as = c'#cs' \<Longrightarrow> upd_cs cs (as@[a]) = cs'"
proof(induct as arbitrary:cs)
  case Nil
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "upd_cs cs [a] = cs'" by simp
 thus ?case by simp
next
  case (Cons a' as')
  note IH = `\<And>cs. upd_cs cs as' = c'#cs' \<Longrightarrow> upd_cs cs (as'@[a]) = cs'`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with `upd_cs cs (a'#as') = c'#cs'`
    have "upd_cs cs as' = c'#cs'" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_cs cs (as'@[a]) = cs'" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Call
    with `upd_cs cs (a'#as') = c'#cs'`
    have "upd_cs (a'#cs) as' = c'#cs'" by simp
    from IH[OF this] have "upd_cs (a'#cs) (as'@[a]) = cs'" .
    with Call show ?thesis by simp
  next
    case Return
    show ?thesis
    proof(cases cs)
      case Nil
      with `upd_cs cs (a'#as') = c'#cs'` Return
      have "upd_cs cs as' = c'#cs'" by simp
      from IH[OF this] have "upd_cs cs (as'@[a]) = cs'" .
      with Nil Return show ?thesis by simp
    next
      case (Cons cx csx)
      with `upd_cs cs (a'#as') = c'#cs'` Return
      have "upd_cs csx as' = c'#cs'" by simp
      from IH[OF this] have "upd_cs csx (as'@[a]) = cs'" .
      with Cons Return show ?thesis by simp
    qed
  qed
qed


lemma upd_cs_snoc_Call:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_cs cs (as@[a]) = a#(upd_cs cs as)"
proof(induct as arbitrary:cs)
  case Nil
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?case by simp
next
  case (Cons a' as')
  note IH = `\<And>cs. upd_cs cs (as'@[a]) = a#upd_cs cs as'`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra 
    with IH[of cs] show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Call
    with IH[of "a'#cs"] show ?thesis by simp
  next
    case Return
    show ?thesis
    proof(cases cs)
      case Nil
      with IH[of "[]"] Return show ?thesis by simp
    next
      case (Cons cx csx)
      with IH[of csx] Return show ?thesis by simp
    qed
  qed
qed





lemma valid_path_aux_split:
  assumes "valid_path_aux cs (as@as')"
  shows "valid_path_aux cs as" and "valid_path_aux (upd_cs cs as) as'"
  using `valid_path_aux cs (as@as')`
proof(induct cs "as@as'" arbitrary:as as' rule:vpa_induct)
  case (vpa_intra cs a as as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux cs xs`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs cs xs) ys`
  { case 1
    from vpa_intra
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF `as = xs@as'`] have "valid_path_aux cs xs" .
      with `a#xs = as''` `intra_kind (kind a)`
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    from vpa_intra
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs cs []) (tl as')" by simp
      with `as'' = [] \<and> a#as = as'` `intra_kind (kind a)`
      show ?thesis by(fastforce simp:intra_kind_def)
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF `as = xs@as'`] have "valid_path_aux (upd_cs cs xs) as'" .
      from `a#xs = as''` `intra_kind (kind a)` 
      have "upd_cs cs xs = upd_cs cs as''" by(fastforce simp:intra_kind_def)
      with `valid_path_aux (upd_cs cs xs) as'`
      show ?thesis by simp
    qed
  }
next
  case (vpa_Call cs a as Q r p fs as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (a#cs) xs`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow>   valid_path_aux (upd_cs (a#cs) xs) ys`
  { case 1
    from vpa_Call
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF `as = xs@as'`] have "valid_path_aux (a#cs) xs" .
      with `a#xs = as''`[THEN sym] `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      show ?thesis by simp
    qed
  next
    case 2
    from vpa_Call
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs (a#cs) []) (tl as')" .
      with `as'' = [] \<and> a#as = as'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      show ?thesis by clarsimp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF `as = xs@as'`] have "valid_path_aux (upd_cs (a # cs) xs) as'" .
      with `a#xs = as''`[THEN sym]  `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      show ?thesis by simp
    qed
  }
next
  case (vpa_ReturnEmpty cs a as Q p f as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux [] xs`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs [] xs) ys`
  { case 1
    from vpa_ReturnEmpty
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF `as = xs@as'`] have "valid_path_aux [] xs" .
      with `a#xs = as''`[THEN sym] `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = []`
      show ?thesis by simp
    qed
  next
    case 2
    from vpa_ReturnEmpty
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux [] (tl as')" by simp
      with `as'' = [] \<and> a#as = as'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = []`
      show ?thesis by fastforce
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF `as = xs@as'`] have "valid_path_aux (upd_cs [] xs) as'" .
      from `a#xs = as''`[THEN sym] `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = []`
      have "upd_cs [] xs = upd_cs cs as''" by simp
      with `valid_path_aux (upd_cs [] xs) as'` show ?thesis by simp
    qed
  }
next
  case (vpa_ReturnCons cs a as Q p f c' cs' as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux cs' xs`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs cs' xs) ys`
  { case 1
    from vpa_ReturnCons
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
       assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
       then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
       from IH1[OF `as = xs@as'`] have "valid_path_aux cs' xs" .
       with `a#xs = as''`[THEN sym] `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
         `a \<in> get_return_edges c'`
       show ?thesis by simp
     qed
   next
     case 2
     from vpa_ReturnCons
     have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs cs' []) (tl as')" .
       with `as'' = [] \<and> a#as = as'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
         `a \<in> get_return_edges c'`
       show ?thesis by fastforce
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF `as = xs@as'`] have "valid_path_aux (upd_cs cs' xs) as'" .
      from `a#xs = as''`[THEN sym] `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
      have "upd_cs cs' xs = upd_cs cs as''" by simp
      with `valid_path_aux (upd_cs cs' xs) as'` show ?thesis by simp
    qed
  }
qed simp_all


lemma valid_path_aux_Append:
  "\<lbrakk>valid_path_aux cs as; valid_path_aux (upd_cs cs as) as'\<rbrakk>
  \<Longrightarrow> valid_path_aux cs (as@as')"
by(induct rule:vpa_induct,auto simp:intra_kind_def)


lemma vpa_snoc_Call:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "valid_path_aux cs as \<Longrightarrow> valid_path_aux cs (as@[a])"
proof(induct rule:vpa_induct)
  case (vpa_empty cs)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "valid_path_aux cs [a]" by simp
  thus ?case by simp
next
  case (vpa_intra cs a' as')
  from `valid_path_aux cs (as'@[a])` `intra_kind (kind a')`
  have "valid_path_aux cs (a'#(as'@[a]))"
    by(fastforce simp:intra_kind_def)
  thus ?case by simp
next
  case (vpa_Call cs a' as' Q' r' p' fs')
  from `valid_path_aux (a'#cs) (as'@[a])` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
next
  case (vpa_ReturnEmpty cs a' as' Q' p' f')
  from `valid_path_aux [] (as'@[a])` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'` `cs = []`
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
next
  case (vpa_ReturnCons cs a' as' Q' p' f' c' cs')
  from `valid_path_aux cs' (as'@[a])` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'` `cs = c'#cs'`
    `a' \<in> get_return_edges c'`
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
qed



definition valid_path :: "'edge list \<Rightarrow> bool"
  where "valid_path as \<equiv> valid_path_aux [] as"


lemma valid_path_aux_valid_path:
  "valid_path_aux cs as \<Longrightarrow> valid_path as"
by(fastforce intro:valid_path_aux_callstack_prefix simp:valid_path_def)

lemma valid_path_split:
  assumes "valid_path (as@as')" shows "valid_path as" and "valid_path as'"
  using `valid_path (as@as')`
  apply(auto simp:valid_path_def)
   apply(erule valid_path_aux_split)
  apply(drule valid_path_aux_split(2))
  by(fastforce intro:valid_path_aux_callstack_prefix)



definition valid_path' :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>\<^sub>\<surd>* _" [51,0,0] 80)
where vp_def:"n -as\<rightarrow>\<^sub>\<surd>* n' \<equiv> n -as\<rightarrow>* n' \<and> valid_path as"


lemma intra_path_vp:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" shows "n -as\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
    by(simp_all add:intra_path_def)
  from `\<forall>a \<in> set as. intra_kind(kind a)` have "valid_path_aux [] as"
    by(rule valid_path_aux_intra_path)
  thus ?thesis using `n -as\<rightarrow>* n'` by(simp add:vp_def valid_path_def)
qed


lemma vp_split_Cons:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* n'" and "as \<noteq> []"
  obtains a' as' where "as = a'#as'" and "n = sourcenode a'"
  and "valid_edge a'" and "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'"
proof(atomize_elim)
  from `n -as\<rightarrow>\<^sub>\<surd>* n'` `as \<noteq> []` obtain a' as' where "as = a'#as'"
    and "n = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(fastforce elim:path_split_Cons simp:vp_def)
  from `n -as\<rightarrow>\<^sub>\<surd>* n'` have "valid_path as" by(simp add:vp_def)
  from `as = a'#as'` have "as = [a']@as'" by simp
  with `valid_path as` have "valid_path ([a']@as')" by simp
  hence "valid_path as'" by(rule valid_path_split)
  with `targetnode a' -as'\<rightarrow>* n'` have "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'" by(simp add:vp_def)
  with `as = a'#as'` `n = sourcenode a'` `valid_edge a'`
  show "\<exists>a' as'. as = a'#as' \<and> n = sourcenode a' \<and> valid_edge a' \<and> 
                 targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'" by blast
qed

lemma vp_split_snoc:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof(atomize_elim)
  from `n -as\<rightarrow>\<^sub>\<surd>* n'` `as \<noteq> []` obtain a' as' where "as = as'@[a']"
    and "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "n' = targetnode a'"
    by(clarsimp simp:vp_def)(erule path_split_snoc,auto)
  from `n -as\<rightarrow>\<^sub>\<surd>* n'` `as = as'@[a']` have "valid_path (as'@[a'])" by(simp add:vp_def)
  hence "valid_path as'" by(rule valid_path_split)
  with `n -as'\<rightarrow>* sourcenode a'` have "n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" by(simp add:vp_def)
  with `as = as'@[a']` `valid_edge a'` `n' = targetnode a'`
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a' \<and> valid_edge a' \<and> 
                 n' = targetnode a'"
  by blast
qed

lemma vp_split:
  assumes "n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'"
  shows "n -as\<rightarrow>\<^sub>\<surd>* sourcenode a" and "valid_edge a" and "targetnode a -as'\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from `n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a" 
    and "targetnode a -as'\<rightarrow>* n'"
    by(auto intro:path_split simp:vp_def)
  from `n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'` have "valid_path (as@a#as')" by(simp add:vp_def)
  hence "valid_path as" and "valid_path (a#as')" by(auto intro:valid_path_split)
  from `valid_path (a#as')` have "valid_path ([a]@as')" by simp
  hence "valid_path as'"  by(rule valid_path_split)
  with `n -as\<rightarrow>* sourcenode a` `valid_path as` `valid_edge a` `targetnode a -as'\<rightarrow>* n'`
  show "n -as\<rightarrow>\<^sub>\<surd>* sourcenode a" "valid_edge a" "targetnode a -as'\<rightarrow>\<^sub>\<surd>* n'"
    by(auto simp:vp_def)
qed

lemma vp_split_second:
  assumes "n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'" shows "sourcenode a -a#as'\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from `n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'` have "sourcenode a -a#as'\<rightarrow>* n'"
    by(fastforce elim:path_split_second simp:vp_def)
  from `n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'` have "valid_path (as@a#as')" by(simp add:vp_def)
  hence "valid_path (a#as')" by(rule valid_path_split)
  with `sourcenode a -a#as'\<rightarrow>* n'` show ?thesis by(simp add:vp_def)
qed




function valid_path_rev_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "valid_path_rev_aux cs [] \<longleftrightarrow> True"
  | "valid_path_rev_aux cs (as@[a]) \<longleftrightarrow> 
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> valid_path_rev_aux (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> valid_path_rev_aux [] as
                                     | c'#cs' \<Rightarrow> c' \<in> get_return_edges a \<and>
                                                 valid_path_rev_aux cs' as
                       |    _ \<Rightarrow> valid_path_rev_aux cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order



lemma vpra_induct [consumes 1,case_names vpra_empty vpra_intra vpra_Return 
  vpra_CallEmpty vpra_CallCons]:
  assumes major: "valid_path_rev_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); valid_path_rev_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; valid_path_rev_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = []; valid_path_rev_aux [] as; 
         P [] as\<rbrakk> \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs c' cs'. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = c'#cs'; 
         valid_path_rev_aux cs' as; c' \<in> get_return_edges a; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (as@[a])"
  shows "P xs ys"
using major
apply(induct ys arbitrary:xs rule:rev_induct)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma vpra_callstack_prefix:
  "valid_path_rev_aux (cs@cs') as \<Longrightarrow> valid_path_rev_aux cs as"
proof(induct "cs@cs'" as arbitrary:cs cs' rule:vpra_induct)
  case vpra_empty thus ?case by simp
next
  case (vpra_intra a as)
  hence "valid_path_rev_aux cs as" by simp
  with `intra_kind (kind a)` show ?case by(fastforce simp:intra_kind_def)
next
  case (vpra_Return a as Q p f)
  note IH = `\<And>ds ds'. a#cs@cs' = ds@ds' \<Longrightarrow> valid_path_rev_aux ds as`
  have "a#cs@cs' = (a#cs)@cs'" by simp
  from IH[OF this] have "valid_path_rev_aux (a#cs) as" .
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show ?case by simp
next
  case (vpra_CallEmpty a as Q r p fs)
  hence "valid_path_rev_aux cs as" by simp
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs@cs' = []` show ?case by simp
next
  case (vpra_CallCons a as Q r p fs c' csx)
  note IH = `\<And>cs cs'. csx = cs@cs' \<Longrightarrow> valid_path_rev_aux cs as`
  from `cs@cs' = c'#csx`
  have "(cs = [] \<and> cs' = c'#csx) \<or> (\<exists>zs. cs = c'#zs \<and> zs@cs' = csx)"
    by(simp add:append_eq_Cons_conv)
  thus ?case
  proof
    assume "cs = [] \<and> cs' = c'#csx"
    hence "cs = []" and "cs' = c'#csx" by simp_all
    from `cs' = c'#csx` have "csx = []@tl cs'" by simp
    from IH[OF this] have "valid_path_rev_aux [] as" .
    with `cs = []` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?thesis by simp
  next
    assume "\<exists>zs. cs = c'#zs \<and> zs@cs' = csx"
    then obtain zs where "cs = c'#zs" and "csx = zs@cs'" by auto
    from IH[OF `csx = zs@cs'`] have "valid_path_rev_aux zs as" .
    with `cs = c'#zs` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `c' \<in> get_return_edges a` show ?thesis by simp
  qed
qed



function upd_rev_cs :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "upd_rev_cs cs [] = cs"
  | "upd_rev_cs cs (as@[a]) =
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> upd_rev_cs (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> upd_rev_cs cs as
                                      | c'#cs' \<Rightarrow> upd_rev_cs cs' as
                       |    _ \<Rightarrow> upd_rev_cs cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order


lemma upd_rev_cs_empty [dest]:
  "upd_rev_cs cs [] = [] \<Longrightarrow> cs = []"
by(cases cs) auto


lemma valid_path_rev_aux_split:
  assumes "valid_path_rev_aux cs (as@as')"
  shows "valid_path_rev_aux cs as'" and "valid_path_rev_aux (upd_rev_cs cs as') as"
  using `valid_path_rev_aux cs (as@as')`
proof(induct cs "as@as'" arbitrary:as as' rule:vpra_induct)
  case (vpra_intra cs a as as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux cs ys`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs cs ys) xs`
  { case 1
    from vpra_intra
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF `as = as''@xs`] have "valid_path_rev_aux cs xs" .
      with `xs@[a] = as'` `intra_kind (kind a)`
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    from vpra_intra
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] have "valid_path_rev_aux (upd_rev_cs cs []) (butlast as'')" .
      with `as' = [] \<and> as@[a] = as''` `intra_kind (kind a)`
      show ?thesis by(fastforce simp:intra_kind_def)
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF `as = as''@xs`] have "valid_path_rev_aux (upd_rev_cs cs xs) as''" .
      from `xs@[a] = as'` `intra_kind (kind a)` 
      have "upd_rev_cs cs xs = upd_rev_cs cs as'" by(fastforce simp:intra_kind_def)
      with `valid_path_rev_aux (upd_rev_cs cs xs) as''`
      show ?thesis by simp
    qed
  }
next
  case (vpra_Return cs a as Q p f as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (a#cs) ys`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs (a#cs) ys) xs`
  { case 1
    from vpra_Return
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF `as = as''@xs`] have "valid_path_rev_aux (a#cs) xs" .
      with `xs@[a] = as'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_Return
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs (a#cs) []) (butlast as'')" .
      with `as' = [] \<and> as@[a] = as''` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF `as = as''@xs`] 
      have "valid_path_rev_aux (upd_rev_cs (a#cs) xs) as''" .
      from `xs@[a] = as'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "upd_rev_cs (a#cs) xs = upd_rev_cs cs as'" by fastforce
      with `valid_path_rev_aux (upd_rev_cs (a#cs) xs) as''`
      show ?thesis by simp
    qed
  }
next
  case (vpra_CallEmpty cs a as Q r p fs as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux [] ys`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs [] ys) xs`
  { case 1
    from vpra_CallEmpty
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF `as = as''@xs`] have "valid_path_rev_aux [] xs" .
      with `xs@[a] = as'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = []`
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_CallEmpty
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs [] []) (butlast as'')" .
      with `as' = [] \<and> as@[a] = as''` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = []`
      show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF `as = as''@xs`] 
      have "valid_path_rev_aux (upd_rev_cs [] xs) as''" .
      with `xs@[a] = as'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = []` 
      show ?thesis by fastforce
    qed
  }
next
  case (vpra_CallCons cs a as Q r p fs c' cs' as'')
  note IH1 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux cs' ys`
  note IH2 = `\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs cs' ys) xs`
  { case 1
    from vpra_CallCons
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF `as = as''@xs`] have "valid_path_rev_aux cs' xs" .
      with `xs@[a] = as'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = c' # cs'` `c' \<in> get_return_edges a`
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_CallCons
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs cs' []) (butlast as'')" .
      with `as' = [] \<and> as@[a] = as''` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = c' # cs'`
        `c' \<in> get_return_edges a` show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF `as = as''@xs`] 
      have "valid_path_rev_aux (upd_rev_cs cs' xs) as''" .
      with `xs@[a] = as'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = c' # cs'`
        `c' \<in> get_return_edges a`
      show ?thesis by fastforce
    qed
  }
qed simp_all


lemma valid_path_rev_aux_Append:
  "\<lbrakk>valid_path_rev_aux cs as'; valid_path_rev_aux (upd_rev_cs cs as') as\<rbrakk>
  \<Longrightarrow> valid_path_rev_aux cs (as@as')"
by(induct rule:vpra_induct,
   auto simp:intra_kind_def simp del:append_assoc simp:append_assoc[THEN sym])


lemma vpra_Cons_intra:
  assumes "intra_kind(kind a)"
  shows "valid_path_rev_aux cs as \<Longrightarrow> valid_path_rev_aux cs (a#as)"
proof(induct rule:vpra_induct)
  case (vpra_empty cs)
  have "valid_path_rev_aux cs []" by simp
  with `intra_kind(kind a)` have "valid_path_rev_aux cs ([]@[a])"
    by(simp only:valid_path_rev_aux.simps intra_kind_def,fastforce)
  thus ?case by simp
qed(simp only:append_Cons[THEN sym] valid_path_rev_aux.simps intra_kind_def,fastforce)+


lemma vpra_Cons_Return:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "valid_path_rev_aux cs as \<Longrightarrow> valid_path_rev_aux cs (a#as)"
proof(induct rule:vpra_induct)
  case (vpra_empty cs)
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "valid_path_rev_aux cs ([]@[a])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_intra cs a' as')
  from `valid_path_rev_aux cs (a#as')` `intra_kind (kind a')`
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,fastforce simp:intra_kind_def)
  thus ?case by simp
next
  case (vpra_Return cs a' as' Q' p' f')
  from `valid_path_rev_aux (a'#cs) (a#as')` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'`
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_CallEmpty cs a' as' Q' r' p' fs')
  from `valid_path_rev_aux [] (a#as')` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `cs = []`
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_CallCons cs a' as' Q' r' p' fs' c' cs')
  from `valid_path_rev_aux cs' (a#as')` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `cs = c'#cs'`
    `c' \<in> get_return_edges a'`
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
qed


(*<*)
lemmas append_Cons_rev = append_Cons[THEN sym]
declare append_Cons [simp del] append_Cons_rev [simp]
(*>*)

lemma upd_rev_cs_Cons_intra:
  assumes "intra_kind(kind a)" shows "upd_rev_cs cs (a#as) = upd_rev_cs cs as"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  from `intra_kind (kind a)`
  have "upd_rev_cs cs ([]@[a]) = upd_rev_cs cs []"
    by(simp only:upd_rev_cs.simps,auto simp:intra_kind_def)
  thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>cs. upd_rev_cs cs (a#as') = upd_rev_cs cs as'`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    from IH have "upd_rev_cs cs (a#as') = upd_rev_cs cs as'" .
    with Intra have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
      by(fastforce simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Return
    from IH have "upd_rev_cs (a'#cs) (a#as') = upd_rev_cs (a'#cs) as'" .
    with Return have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
      by(auto simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      from IH have "upd_rev_cs [] (a#as') = upd_rev_cs [] as'" .
      with Call Nil have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    next
      case (Cons c' cs')
      from IH have "upd_rev_cs cs' (a#as') = upd_rev_cs cs' as'" .
      with Call Cons have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    qed
  qed
qed



lemma upd_rev_cs_Cons_Return:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" shows "upd_rev_cs cs (a#as) = a#(upd_rev_cs cs as)"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "upd_rev_cs cs ([]@[a]) = a#(upd_rev_cs cs [])"
    by(simp only:upd_rev_cs.simps) clarsimp
  thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>cs. upd_rev_cs cs (a#as') = a#upd_rev_cs cs as'`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    from IH have "upd_rev_cs cs (a#as') = a#(upd_rev_cs cs as')" .
    with Intra have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
      by(fastforce simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Return
    from IH have "upd_rev_cs (a'#cs) (a#as') = a#(upd_rev_cs (a'#cs) as')" .
    with Return have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
      by(auto simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      from IH have "upd_rev_cs [] (a#as') = a#(upd_rev_cs [] as')" .
      with Call Nil have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    next
      case (Cons c' cs')
      from IH have "upd_rev_cs cs' (a#as') = a#(upd_rev_cs cs' as')" .
      with Call Cons 
      have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma upd_rev_cs_Cons_Call_Cons:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_rev_cs cs as = c'#cs' \<Longrightarrow> upd_rev_cs cs (a#as) = cs'"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_rev_cs cs ([]@[a]) = cs'"
    by(simp only:upd_rev_cs.simps) clarsimp
 thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>cs. upd_rev_cs cs as' = c'#cs' \<Longrightarrow> upd_rev_cs cs (a#as') = cs'`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with `upd_rev_cs cs (as'@[a']) = c'#cs'`
    have "upd_rev_cs cs as' = c'#cs'" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_rev_cs cs (a#as') = cs'" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Return
    with `upd_rev_cs cs (as'@[a']) = c'#cs'`
    have "upd_rev_cs (a'#cs) as' = c'#cs'" by simp
    from IH[OF this] have "upd_rev_cs (a'#cs) (a#as') = cs'" .
    with Return show ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      with `upd_rev_cs cs (as'@[a']) = c'#cs'` Call
      have "upd_rev_cs cs as' = c'#cs'" by simp
      from IH[OF this] have "upd_rev_cs cs (a#as') = cs'" .
      with Nil Call show ?thesis by simp
    next
      case (Cons cx csx)
      with `upd_rev_cs cs (as'@[a']) = c'#cs'` Call
      have "upd_rev_cs csx as' = c'#cs'" by simp
      from IH[OF this] have "upd_rev_cs csx (a#as') = cs'" .
      with Cons Call show ?thesis by simp
    qed
  qed
qed


lemma upd_rev_cs_Cons_Call_Cons_Empty:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_rev_cs cs as = [] \<Longrightarrow> upd_rev_cs cs (a#as) = []"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_rev_cs cs ([]@[a]) = []"
    by(simp only:upd_rev_cs.simps) clarsimp
 thus ?case by simp
next
  case (snoc a' as')
  note IH = `\<And>cs. upd_rev_cs cs as' = [] \<Longrightarrow> upd_rev_cs cs (a#as') = []`
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with `upd_rev_cs cs (as'@[a']) = []`
    have "upd_rev_cs cs as' = []" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_rev_cs cs (a#as') = []" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Return
    with `upd_rev_cs cs (as'@[a']) = []`
    have "upd_rev_cs (a'#cs) as' = []" by simp
    from IH[OF this] have "upd_rev_cs (a'#cs) (a#as') = []" .
    with Return show ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      with `upd_rev_cs cs (as'@[a']) = []` Call
      have "upd_rev_cs cs as' = []" by simp
      from IH[OF this] have "upd_rev_cs cs (a#as') = []" .
      with Nil Call show ?thesis by simp
    next
      case (Cons cx csx)
      with `upd_rev_cs cs (as'@[a']) = []` Call
      have "upd_rev_cs csx as' = []" by simp
      from IH[OF this] have "upd_rev_cs csx (a#as') = []" .
      with Cons Call show ?thesis by simp
    qed
  qed
qed

(*<*)declare append_Cons [simp] append_Cons_rev [simp del](*>*)


definition valid_call_list :: "'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  where "valid_call_list cs n \<equiv>
  \<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> (valid_edge c \<and> (\<exists>Q r p fs. (kind c = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> 
                    p = get_proc (case cs' of [] \<Rightarrow> n | _ \<Rightarrow> last (sourcenodes cs'))))"

definition valid_return_list :: "'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  where "valid_return_list cs n \<equiv>
  \<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> (valid_edge c \<and> (\<exists>Q p f. (kind c = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> 
                    p = get_proc (case cs' of [] \<Rightarrow> n | _ \<Rightarrow> last (targetnodes cs'))))"


lemma valid_call_list_valid_edges: 
  assumes "valid_call_list cs n" shows "\<forall>c \<in> set cs. valid_edge c"
proof -
  from `valid_call_list cs n` 
  have "\<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> valid_edge c"
    by(simp add:valid_call_list_def)
  thus ?thesis
  proof(induct cs)
    case Nil thus ?case by simp
  next
    case (Cons cx csx)
    note IH = `\<forall>cs' c cs''. csx = cs'@c#cs'' \<longrightarrow> valid_edge c \<Longrightarrow>
                            \<forall>a\<in>set csx. valid_edge a`
    from `\<forall>cs' c cs''. cx#csx = cs'@c#cs'' \<longrightarrow> valid_edge c`
    have "valid_edge cx" by blast
    from `\<forall>cs' c cs''. cx#csx = cs'@c#cs'' \<longrightarrow> valid_edge c`
    have "\<forall>cs' c cs''. csx = cs'@c#cs'' \<longrightarrow> valid_edge c"
      by auto(erule_tac x="cx#cs'" in allE,auto)
    from IH[OF this] `valid_edge cx` show ?case by simp
  qed
qed


lemma valid_return_list_valid_edges: 
  assumes "valid_return_list rs n" shows "\<forall>r \<in> set rs. valid_edge r"
proof -
  from `valid_return_list rs n` 
  have "\<forall>rs' r rs''. rs = rs'@r#rs'' \<longrightarrow> valid_edge r"
    by(simp add:valid_return_list_def)
  thus ?thesis
  proof(induct rs)
    case Nil thus ?case by simp
  next
    case (Cons rx rsx)
    note IH = `\<forall>rs' r rs''. rsx = rs'@r#rs'' \<longrightarrow> valid_edge r \<Longrightarrow>
                            \<forall>a\<in>set rsx. valid_edge a`
    from `\<forall>rs' r rs''. rx#rsx = rs'@r#rs'' \<longrightarrow> valid_edge r`
    have "valid_edge rx" by blast
    from `\<forall>rs' r rs''. rx#rsx = rs'@r#rs'' \<longrightarrow> valid_edge r`
    have "\<forall>rs' r rs''. rsx = rs'@r#rs'' \<longrightarrow> valid_edge r"
      by auto(erule_tac x="rx#rs'" in allE,auto)
    from IH[OF this] `valid_edge rx` show ?case by simp
  qed
qed


lemma vpra_empty_valid_call_list_rev:
  "valid_call_list cs n \<Longrightarrow> valid_path_rev_aux [] (rev cs)"
proof(induct cs arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons c' cs')
  note IH = `\<And>n. valid_call_list cs' n \<Longrightarrow> valid_path_rev_aux [] (rev cs')`
  from `valid_call_list (c'#cs') n` have "valid_call_list cs' (sourcenode c')"
    apply(clarsimp simp:valid_call_list_def)
    apply hypsubst_thin
    apply(erule_tac x="c'#cs'" in allE)
    apply clarsimp
    by(case_tac cs',auto simp:sourcenodes_def)
  from IH[OF this] have "valid_path_rev_aux [] (rev cs')" .
  moreover
  from `valid_call_list (c'#cs') n` obtain Q r p fs where "kind c' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE) fastforce
  ultimately show ?case by simp
qed


lemma vpa_upd_cs_cases:
  "\<lbrakk>valid_path_aux cs as; valid_call_list cs n; n -as\<rightarrow>* n'\<rbrakk>
  \<Longrightarrow> case (upd_cs cs as) of [] \<Rightarrow> (\<forall>c \<in> set cs. \<exists>a \<in> set as. a \<in> get_return_edges c)
                      | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'"
proof(induct arbitrary:n rule:vpa_induct)
  case (vpa_empty cs)
  from `n -[]\<rightarrow>* n'` have "n = n'" by fastforce
  with `valid_call_list cs n` show ?case by(cases cs) auto
next
  case (vpa_intra cs a' as')
  note IH = `\<And>n. \<lbrakk>valid_call_list cs n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs cs as') of [] \<Rightarrow> \<forall>c\<in>set cs. \<exists>a\<in>set as'. a \<in> get_return_edges c
                         | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'`
  from `intra_kind (kind a')` have "upd_cs cs (a'#as') = upd_cs cs as'"
    by(fastforce simp:intra_kind_def)
  from `n -a'#as'\<rightarrow>* n'` have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from `valid_edge a'` `intra_kind (kind a')`
  have "get_proc (sourcenode a') = get_proc (targetnode a')" by(rule get_proc_intra)
  with `valid_call_list cs n` have "valid_call_list cs (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs') auto
  from IH[OF this `targetnode a' -as'\<rightarrow>* n'`] `upd_cs cs (a'#as') = upd_cs cs as'`
  show ?case by(cases "upd_cs cs as'") auto
next
  case (vpa_Call cs a' as' Q r p fs)
  note IH = `\<And>n. \<lbrakk>valid_call_list (a'#cs) n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs (a'#cs) as') 
             of [] \<Rightarrow> \<forall>c\<in>set (a'#cs). \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'`
  from `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs (a'#cs) as' = upd_cs cs (a'#as')"
    by simp
  from `n -a'#as'\<rightarrow>* n'` have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "get_proc (targetnode a') = p" by(rule get_proc_call)
  with `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_call_list cs n`
  have "valid_call_list (a'#cs) (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE) apply clarsimp
    by(case_tac list,auto simp:sourcenodes_def)
  from IH[OF this `targetnode a' -as'\<rightarrow>* n'`] 
    `upd_cs (a'#cs) as' = upd_cs cs (a'#as')`
  have "case upd_cs cs (a'#as') 
         of [] \<Rightarrow> \<forall>c\<in>set (a' # cs). \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx # csx \<Rightarrow> valid_call_list (cx # csx) n'" by simp
  thus ?case by(cases "upd_cs cs (a'#as')") simp+
next
  case (vpa_ReturnEmpty cs a' as' Q p f)
  note IH = `\<And>n. \<lbrakk>valid_call_list [] n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs [] as') 
             of [] \<Rightarrow> \<forall>c\<in>set []. \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'`
  from `kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = []` have "upd_cs [] as' = upd_cs cs (a'#as')"
    by simp
  from `n -a'#as'\<rightarrow>* n'` have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  have "valid_call_list [] (targetnode a')" by(simp add:valid_call_list_def)
  from IH[OF this `targetnode a' -as'\<rightarrow>* n'`]
    `upd_cs [] as' = upd_cs cs (a'#as')`
  have "case (upd_cs cs (a'#as')) 
         of [] \<Rightarrow> \<forall>c\<in>set []. \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'" by simp
  with `cs = []` show ?case by(cases "upd_cs cs (a'#as')") simp+
next
  case (vpa_ReturnCons cs a' as' Q p f c' cs')
  note IH = `\<And>n. \<lbrakk>valid_call_list cs' n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs cs' as') 
             of [] \<Rightarrow> \<forall>c\<in>set cs'. \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'`
  from `kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` `a' \<in> get_return_edges c'` 
  have "upd_cs cs' as' = upd_cs cs (a'#as')" by simp
  from `n -a'#as'\<rightarrow>* n'` have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from `valid_call_list cs n` `cs = c'#cs'` have "valid_edge c'"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE,auto)
  with `a' \<in> get_return_edges c'` obtain ax where "valid_edge ax"
    and sources:"sourcenode ax = sourcenode c'" 
    and targets:"targetnode ax = targetnode a'" and "kind ax = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from `valid_edge ax` sources[THEN sym] targets[THEN sym] `kind ax = (\<lambda>cf. False)\<^sub>\<surd>`
  have "get_proc (sourcenode c') = get_proc (targetnode a')"
    by(fastforce intro:get_proc_intra simp:intra_kind_def)
  with `valid_call_list cs n` `cs = c'#cs'`
  have "valid_call_list cs' (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(hypsubst_thin)
    apply(erule_tac x="c'#cs'" in allE)
    by(case_tac cs',auto simp:sourcenodes_def)
  from IH[OF this `targetnode a' -as'\<rightarrow>* n'`] 
    `upd_cs cs' as' = upd_cs cs (a'#as')`
  have "case (upd_cs cs (a'#as')) 
         of [] \<Rightarrow> \<forall>c\<in>set cs'. \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'" by simp
  with `cs = c' # cs'` `a' \<in> get_return_edges c'` show ?case
    by(cases "upd_cs cs (a'#as')") simp+
qed


lemma vpa_valid_call_list_valid_return_list_vpra:
  "\<lbrakk>valid_path_aux cs cs'; valid_call_list cs n; valid_return_list cs' n'\<rbrakk>
  \<Longrightarrow> valid_path_rev_aux cs' (rev cs)"
proof(induct arbitrary:n n' rule:vpa_induct)
  case (vpa_empty cs)
  from `valid_call_list cs n` show ?case by(rule vpra_empty_valid_call_list_rev)
next
  case (vpa_intra cs a as)
  from `intra_kind (kind a)` `valid_return_list (a#as) n'`
  have False apply(clarsimp simp:valid_return_list_def)
    by(erule_tac x="[]" in allE,clarsimp simp:intra_kind_def)
  thus ?case by simp
next
  case (vpa_Call cs a as Q r p fs)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_return_list (a#as) n'`
  have False apply(clarsimp simp:valid_return_list_def)
    by(erule_tac x="[]" in allE,clarsimp)
  thus ?case by simp
next
  case (vpa_ReturnEmpty cs a as Q p f)
  from `cs = []` show ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f c' cs')
  note IH = `\<And>n n'. \<lbrakk>valid_call_list cs' n; valid_return_list as n'\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux as (rev cs')`
  from `valid_return_list (a#as) n'` have "valid_return_list as (targetnode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="a#cs'" in allE)
    by(case_tac cs',auto simp:targetnodes_def)
  from `valid_call_list cs n` `cs = c'#cs'`
  have "valid_call_list cs' (sourcenode c')"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="c'#cs'" in allE)
    by(case_tac cs',auto simp:sourcenodes_def)
  from `valid_call_list cs n` `cs = c'#cs'` have "valid_edge c'"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE,auto)
  with `a \<in> get_return_edges c'` obtain Q' r' p' f' where "kind c' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'"
    apply(cases "kind c'" rule:edge_kind_cases)
    by(auto dest:only_call_get_return_edges simp:intra_kind_def)
  from IH[OF `valid_call_list cs' (sourcenode c')`
    `valid_return_list as (targetnode a)`]
  have "valid_path_rev_aux as (rev cs')" .
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` `a \<in> get_return_edges c'` `kind c' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'`
  show ?case by simp
qed
 


lemma vpa_to_vpra:
  "\<lbrakk>valid_path_aux cs as; valid_path_aux (upd_cs cs as) cs'; 
    n -as\<rightarrow>* n'; valid_call_list cs n; valid_return_list cs' n''\<rbrakk> 
  \<Longrightarrow> valid_path_rev_aux cs' as \<and> valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)"
proof(induct arbitrary:n rule:vpa_induct)
  case vpa_empty thus ?case
    by(fastforce intro:vpa_valid_call_list_valid_return_list_vpra)
next
  case (vpa_intra cs a as)
  note IH = `\<And>n. \<lbrakk>valid_path_aux (upd_cs cs as) cs'; n -as\<rightarrow>* n';
    valid_call_list cs n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)`
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with `valid_call_list cs n` `n = sourcenode a`
  have "valid_call_list cs (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs') auto
  from `valid_path_aux (upd_cs cs (a#as)) cs'` `intra_kind (kind a)`
  have "valid_path_aux (upd_cs cs as) cs'"
    by(fastforce simp:intra_kind_def)
  from IH[OF this `targetnode a -as\<rightarrow>* n'` `valid_call_list cs (targetnode a)`
    `valid_return_list cs' n''`]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)" by simp_all
  from  `intra_kind (kind a)` `valid_path_rev_aux cs' as`
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_intra)
  from `intra_kind (kind a)` have "upd_rev_cs cs' (a#as) = upd_rev_cs cs' as"
    by(simp add:upd_rev_cs_Cons_intra)
  with `valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)`
  have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
  with `valid_path_rev_aux cs' (a#as)` show ?case by simp
next
  case (vpa_Call cs a as Q r p fs)
  note IH = `\<And>n. \<lbrakk>valid_path_aux (upd_cs (a#cs) as) cs'; n -as\<rightarrow>* n';
    valid_call_list (a#cs) n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))`
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "p = get_proc (targetnode a)"
    by(rule get_proc_call[THEN sym])
  from `valid_call_list cs n` `n = sourcenode a`
  have "valid_call_list cs (sourcenode a)" by simp
  with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge a` `p = get_proc (targetnode a)`
  have "valid_call_list (a#cs) (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE) apply clarsimp
    by(case_tac list,auto simp:sourcenodes_def)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs cs (a#as) = upd_cs (a#cs) as"
    by simp
  with `valid_path_aux (upd_cs cs (a#as)) cs'`
  have "valid_path_aux (upd_cs (a#cs) as) cs'" by simp
  from IH[OF this `targetnode a -as\<rightarrow>* n'` `valid_call_list (a#cs) (targetnode a)`
    `valid_return_list cs' n''`]
  have "valid_path_rev_aux cs' as"
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))" by simp_all
  show ?case
  proof(cases "upd_rev_cs cs' as")
    case Nil
    with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "upd_rev_cs cs' (a#as) = []" by(rule upd_rev_cs_Cons_Call_Cons_Empty)
    with `valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` Nil
    have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
    from Nil `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "valid_path_rev_aux (upd_rev_cs cs' as) ([]@[a])"
      by(simp only:valid_path_rev_aux.simps) clarsimp
    with `valid_path_rev_aux cs' as` have "valid_path_rev_aux cs' ([a]@as)"
      by(fastforce intro:valid_path_rev_aux_Append)
    with `valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)`
    show ?thesis by simp
  next
    case (Cons cx csx)
    with `valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have match:"cx \<in> get_return_edges a" "valid_path_rev_aux csx (rev cs)" by auto
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` Cons have "upd_rev_cs cs' (a#as) = csx"
      by(rule upd_rev_cs_Cons_Call_Cons)
    with `valid_path_rev_aux (upd_rev_cs cs' as) (rev(a#cs))` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` match
    have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
    from Cons `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` match
    have "valid_path_rev_aux (upd_rev_cs cs' as) ([]@[a])"
      by(simp only:valid_path_rev_aux.simps) clarsimp
    with `valid_path_rev_aux cs' as` have "valid_path_rev_aux cs' ([a]@as)"
      by(fastforce intro:valid_path_rev_aux_Append)
    with `valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)`
    show ?thesis by simp
  qed
next
  case (vpa_ReturnEmpty cs a as Q p f)
  note IH = `\<And>n. \<lbrakk>valid_path_aux (upd_cs [] as) cs'; n -as\<rightarrow>* n';
    valid_call_list [] n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev [])`
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from `cs = []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "upd_cs cs (a#as) = upd_cs [] as"
    by simp
  with `valid_path_aux (upd_cs cs (a#as)) cs'`
  have "valid_path_aux (upd_cs [] as) cs'" by simp
  from IH[OF this `targetnode a -as\<rightarrow>* n'` _ `valid_return_list cs' n''`]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev [])" 
    by(auto simp:valid_call_list_def)
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `valid_path_rev_aux cs' as`
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_Return)
  moreover
  from `cs = []` have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)"
    by simp
  ultimately show ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f cx csx)
  note IH = `\<And>n. \<lbrakk>valid_path_aux (upd_cs csx as) cs'; n -as\<rightarrow>* n';
    valid_call_list csx n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)`
  note match = `cs = cx#csx` `a \<in> get_return_edges cx`
  from `n -a#as\<rightarrow>* n'` have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from `cs = cx#csx` `valid_call_list cs n` have "valid_edge cx"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE) clarsimp
  with match have "get_proc (sourcenode cx) = get_proc (targetnode a)"
    by(fastforce intro:get_proc_get_return_edge)
  with `valid_call_list cs n` `cs = cx#csx`
  have "valid_call_list csx (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cx#cs'" in allE) apply clarsimp
    by(case_tac cs',auto simp:sourcenodes_def)
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` match have "upd_cs cs (a#as) = upd_cs csx as" by simp
  with `valid_path_aux (upd_cs cs (a#as)) cs'`
  have "valid_path_aux (upd_cs csx as) cs'" by simp
  from IH[OF this `targetnode a -as\<rightarrow>* n'` `valid_call_list csx (targetnode a)`
    `valid_return_list cs' n''`]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)" by simp_all
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `valid_path_rev_aux cs' as`
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_Return)
  from match `valid_edge cx` obtain Q' r' p' f' where "kind cx = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'"
    by(fastforce dest!:only_call_get_return_edges)
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "upd_rev_cs cs' (a#as) = a#(upd_rev_cs cs' as)"
    by(rule upd_rev_cs_Cons_Return)
  with `valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` 
    `kind cx = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'` match
  have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)"
    by simp
  with `valid_path_rev_aux cs' (a#as)` show ?case by simp
qed


lemma vp_to_vpra:
  "n -as\<rightarrow>\<^sub>\<surd>* n' \<Longrightarrow> valid_path_rev_aux [] as"
by(fastforce elim:vpa_to_vpra[THEN conjunct1] 
            simp:vp_def valid_path_def valid_call_list_def valid_return_list_def)




subsubsection {* Same level paths *}


fun same_level_path_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "same_level_path_aux cs [] \<longleftrightarrow> True"
  | "same_level_path_aux cs (a#as) \<longleftrightarrow> 
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> same_level_path_aux (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> False
                                     | c'#cs' \<Rightarrow> a \<in> get_return_edges c' \<and>
                                             same_level_path_aux cs' as
                       |    _ \<Rightarrow> same_level_path_aux cs as)"


lemma slpa_induct [consumes 1,case_names slpa_empty slpa_intra slpa_Call 
  slpa_Return]:
  assumes major: "same_level_path_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); same_level_path_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; same_level_path_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f c' cs'. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = c'#cs'; same_level_path_aux cs' as;
                             a \<in> get_return_edges c'; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (a#as)"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma slpa_cases [consumes 4,case_names intra_path return_intra_path]:
  assumes "same_level_path_aux cs as" and "upd_cs cs as = []"
  and "\<forall>c \<in> set cs. valid_edge c" and "\<forall>a \<in> set as. valid_edge a"
  obtains "\<forall>a \<in> set as. intra_kind(kind a)"
  | asx a asx' Q p f c' cs' where "as = asx@a#asx'" and "same_level_path_aux cs asx"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "upd_cs cs asx = c'#cs'" and "upd_cs cs (asx@[a]) = []" 
    and "a \<in> get_return_edges c'" and "valid_edge c'"
    and "\<forall>a \<in> set asx'. intra_kind(kind a)"
proof(atomize_elim)
  from assms
  show "(\<forall>a\<in>set as. intra_kind (kind a)) \<or>
    (\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
       kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> upd_cs cs asx = c'#cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
       a \<in> get_return_edges c' \<and> valid_edge c' \<and> (\<forall>a\<in>set asx'. intra_kind (kind a)))"
  proof(induct rule:slpa_induct)
    case (slpa_empty cs)
    have "\<forall>a\<in>set []. intra_kind (kind a)" by simp
    thus ?case by simp
  next
    case (slpa_intra cs a as)
    note IH = `\<lbrakk>upd_cs cs as = []; \<forall>c\<in>set cs. valid_edge c; \<forall>a'\<in>set as. valid_edge a'\<rbrakk> 
      \<Longrightarrow> (\<forall>a\<in>set as. intra_kind (kind a)) \<or>
      (\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
        kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and>  upd_cs cs asx = c' # cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
        a \<in> get_return_edges c' \<and> valid_edge c' \<and> (\<forall>a\<in>set asx'. intra_kind (kind a)))`
    from `\<forall>a'\<in>set (a#as). valid_edge a'` have "\<forall>a'\<in>set as. valid_edge a'" by simp
    from `intra_kind (kind a)` `upd_cs cs (a#as) = []`
    have "upd_cs cs as = []" by(fastforce simp:intra_kind_def)
    from IH[OF this `\<forall>c\<in>set cs. valid_edge c` `\<forall>a'\<in>set as. valid_edge a'`] show ?case
    proof
      assume "\<forall>a\<in>set as. intra_kind (kind a)"
      with `intra_kind (kind a)` have "\<forall>a'\<in>set (a#as). intra_kind (kind a')"
        by simp
      thus ?case by simp
    next
      assume "\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
                kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> upd_cs cs asx = c'#cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
                a \<in> get_return_edges c' \<and> valid_edge c' \<and> 
                (\<forall>a\<in>set asx'. intra_kind (kind a))"
      then obtain asx a' Q p f asx' c' cs' where "as = asx@a'#asx'" 
        and "same_level_path_aux cs asx" and "upd_cs cs (asx@[a']) = []"
        and "upd_cs cs asx = c'#cs'" and assms:"a' \<in> get_return_edges c'"
        "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f" "valid_edge c'" "\<forall>a\<in>set asx'. intra_kind (kind a)"
        by blast
      from `as = asx@a'#asx'` have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from `intra_kind (kind a)` `same_level_path_aux cs asx`
      have "same_level_path_aux cs (a#asx)" by(fastforce simp:intra_kind_def)
      moreover
      from `upd_cs cs asx = c'#cs'` `intra_kind (kind a)`
      have "upd_cs cs (a#asx) = c'#cs'" by(fastforce simp:intra_kind_def)
      moreover
      from `upd_cs cs (asx@[a']) = []` `intra_kind (kind a)`
      have "upd_cs cs ((a#asx)@[a']) = []" by(fastforce simp:intra_kind_def)
      ultimately show ?case using assms by blast
    qed
  next
    case (slpa_Call cs a as Q r p fs)
    note IH = `\<lbrakk>upd_cs (a#cs) as = []; \<forall>c\<in>set (a#cs). valid_edge c;
      \<forall>a'\<in>set as. valid_edge a'\<rbrakk> \<Longrightarrow> 
      (\<forall>a'\<in>set as. intra_kind (kind a')) \<or>
      (\<exists>asx a' asx' Q' p' f' c' cs'. as = asx@a'#asx' \<and> 
        same_level_path_aux (a#cs) asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> 
        upd_cs (a#cs) asx = c'#cs' \<and> upd_cs (a#cs) (asx@[a']) = [] \<and> 
        a' \<in> get_return_edges c' \<and> valid_edge c' \<and> 
        (\<forall>a'\<in>set asx'. intra_kind (kind a')))`
    from `\<forall>a'\<in>set (a#as). valid_edge a'` have "valid_edge a" 
      and "\<forall>a'\<in>set as. valid_edge a'" by simp_all
    from `\<forall>c\<in>set cs. valid_edge c` `valid_edge a` have "\<forall>c\<in>set (a#cs). valid_edge c"
      by simp
    from `upd_cs cs (a#as) = []` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "upd_cs (a#cs) as = []" by simp
    from IH[OF this `\<forall>c\<in>set (a#cs). valid_edge c` `\<forall>a'\<in>set as. valid_edge a'`]
    show ?case
    proof
      assume "\<forall>a'\<in>set as. intra_kind (kind a')"
      with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs cs (a#as) = a#cs"
        by(fastforce intro:upd_cs_intra_path)
      with `upd_cs cs (a#as) = []` have False by simp
      thus ?case by simp
    next
      assume "\<exists>asx a' asx' Q p f c' cs'. as = asx@a'#asx' \<and> 
                same_level_path_aux (a#cs) asx \<and> kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> 
                upd_cs (a#cs) asx = c'#cs' \<and> upd_cs (a#cs) (asx@[a']) = [] \<and> 
                a' \<in> get_return_edges c' \<and> valid_edge c' \<and> 
                (\<forall>a\<in>set asx'. intra_kind (kind a))"
      then obtain asx a' Q' p' f' asx' c' cs' where "as = asx@a'#asx'" 
        and "same_level_path_aux (a#cs) asx" and "upd_cs (a#cs) (asx@[a']) = []"
        and "upd_cs (a#cs) asx = c'#cs'" and assms:"a' \<in> get_return_edges c'"
        "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" "valid_edge c'" "\<forall>a\<in>set asx'. intra_kind (kind a)"
        by blast
      from `as = asx@a'#asx'` have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `same_level_path_aux (a#cs) asx`
      have "same_level_path_aux cs (a#asx)" by simp
      moreover
      from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs (a#cs) asx = c'#cs'`
      have "upd_cs cs (a#asx) = c'#cs'" by simp
      moreover
      from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs (a#cs) (asx@[a']) = []`
      have "upd_cs cs ((a#asx)@[a']) = []" by simp
      ultimately show ?case using assms by blast
    qed
  next
    case (slpa_Return cs a as Q p f c' cs')
    note IH = `\<lbrakk>upd_cs cs' as = []; \<forall>c\<in>set cs'. valid_edge c; 
      \<forall>a'\<in>set as. valid_edge a'\<rbrakk> \<Longrightarrow> 
      (\<forall>a'\<in>set as. intra_kind (kind a')) \<or>
      (\<exists>asx a' asx' Q' p' f' c'' cs''. as = asx@a'#asx' \<and> 
        same_level_path_aux cs' asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> upd_cs cs' asx = c''#cs'' \<and>
        upd_cs cs' (asx@[a']) = [] \<and> a' \<in> get_return_edges c'' \<and> valid_edge c'' \<and> 
        (\<forall>a'\<in>set asx'. intra_kind (kind a')))`
    from `\<forall>a'\<in>set (a#as). valid_edge a'` have "valid_edge a" 
      and "\<forall>a'\<in>set as. valid_edge a'" by simp_all
    from `\<forall>c\<in>set cs. valid_edge c` `cs = c' # cs'`
    have "valid_edge c'" and "\<forall>c\<in>set cs'. valid_edge c" by simp_all
    from `upd_cs cs (a#as) = []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` 
      `a \<in> get_return_edges c'` have "upd_cs cs' as = []" by simp
    from IH[OF this `\<forall>c\<in>set cs'. valid_edge c` `\<forall>a'\<in>set as. valid_edge a'`] show ?case
    proof
      assume "\<forall>a'\<in>set as. intra_kind (kind a')"
      hence "upd_cs cs' as = cs'" by(rule upd_cs_intra_path)
      with `upd_cs cs' as = []` have "cs' = []" by simp
      with `cs = c'#cs'` `a \<in> get_return_edges c'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "upd_cs cs [a] = []" by simp
      moreover
      from `cs = c'#cs'` have "upd_cs cs [] \<noteq> []" by simp
      moreover
      have "same_level_path_aux cs []" by simp
      ultimately show ?case 
        using `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `\<forall>a'\<in>set as. intra_kind (kind a')` `cs = c'#cs'`
          `a \<in> get_return_edges c'` `valid_edge c'`
        by fastforce
    next
      assume "\<exists>asx a' asx' Q' p' f' c'' cs''. as = asx@a'#asx' \<and>
        same_level_path_aux cs' asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> upd_cs cs' asx = c''#cs'' \<and>
        upd_cs cs' (asx@[a']) = [] \<and> a' \<in> get_return_edges c'' \<and> valid_edge c'' \<and>
        (\<forall>a'\<in>set asx'. intra_kind (kind a'))"
      then obtain asx a' asx' Q' p' f' c'' cs'' where "as = asx@a'#asx'"
        and "same_level_path_aux cs' asx" and "upd_cs cs' asx = c''#cs''" 
        and "upd_cs cs' (asx@[a']) = []" and assms:"a' \<in> get_return_edges c''" 
        "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" "valid_edge c''" "\<forall>a'\<in>set asx'. intra_kind (kind a')"
        by blast
      from `as = asx@a'#asx'` have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from `same_level_path_aux cs' asx` `cs = c'#cs'` `a \<in> get_return_edges c'`
        `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "same_level_path_aux cs (a#asx)" by simp
      moreover
      from `upd_cs cs' asx = c''#cs''` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
      have "upd_cs cs (a#asx) = c''#cs''" by simp
      moreover
      from `upd_cs cs' (asx@[a']) = []` `cs = c'#cs'` `a \<in> get_return_edges c'`
        `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "upd_cs cs ((a#asx)@[a']) = []" by simp
      ultimately show ?case using assms by blast
    qed
  qed
qed


lemma same_level_path_aux_valid_path_aux: 
  "same_level_path_aux cs as \<Longrightarrow> valid_path_aux cs as"
by(induct rule:slpa_induct,auto split:edge_kind.split simp:intra_kind_def)


lemma same_level_path_aux_Append:
  "\<lbrakk>same_level_path_aux cs as; same_level_path_aux (upd_cs cs as) as'\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs (as@as')"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma same_level_path_aux_callstack_Append:
  "same_level_path_aux cs as \<Longrightarrow> same_level_path_aux (cs@cs') as"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma same_level_path_upd_cs_callstack_Append:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = cs'\<rbrakk> 
  \<Longrightarrow> upd_cs (cs@cs'') as = (cs'@cs'')"
by(induct rule:slpa_induct,auto split:edge_kind.split simp:intra_kind_def)


lemma slpa_split:
  assumes "same_level_path_aux cs as" and "as = xs@ys" and "upd_cs cs xs = []"
  shows "same_level_path_aux cs xs" and "same_level_path_aux [] ys"
using assms
proof(induct arbitrary:xs ys rule:slpa_induct)
  case (slpa_empty cs) case 1
  from `[] = xs@ys` show ?case by simp
next
  case (slpa_empty cs) case 2
  from `[] = xs@ys` show ?case by simp
next
  case (slpa_intra cs a as)
  note IH1 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux cs xs`
  note IH2 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux [] ys`
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `intra_kind (kind a)`
      have "upd_cs cs xs' = []" by(fastforce simp:intra_kind_def)
      from IH1[OF `as = xs'@ys` this] have "same_level_path_aux cs xs'" .
      with `a = x'` `intra_kind (kind a)` Cons
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with `upd_cs cs xs = []` have "cs = []" by fastforce
      with Nil `a#as = xs@ys` `same_level_path_aux cs as` `intra_kind (kind a)`
      show ?thesis by(cases ys,auto simp:intra_kind_def)
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `intra_kind (kind a)`
      have "upd_cs cs xs' = []" by(fastforce simp:intra_kind_def)
      from IH2[OF `as = xs'@ys` this] show ?thesis .
    qed
  }
next
  case (slpa_Call cs a as Q r p fs)
  note IH1 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs (a#cs) xs = []\<rbrakk> 
    \<Longrightarrow> same_level_path_aux (a#cs) xs`
  note IH2 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs (a#cs) xs = []\<rbrakk> 
    \<Longrightarrow> same_level_path_aux [] ys`
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "upd_cs (a#cs) xs' = []" by simp
      from IH1[OF `as = xs'@ys` this] have "same_level_path_aux (a#cs) xs'" .
      with `a = x'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` Cons show ?thesis by simp
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with `upd_cs cs xs = []` have "cs = []" by fastforce
      with Nil `a#as = xs@ys` `same_level_path_aux (a#cs) as` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      show ?thesis by(cases ys) auto
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "upd_cs (a#cs) xs' = []" by simp
      from IH2[OF `as = xs'@ys` this] show ?thesis .
    qed
  }
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH1 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs' xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux cs' xs`
  note IH2 = `\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs' xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux [] ys`
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
      have "upd_cs cs' xs' = []" by simp
      from IH1[OF `as = xs'@ys` this] have "same_level_path_aux cs' xs'" .
      with `a = x'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` `a \<in> get_return_edges c'` Cons 
      show ?thesis by simp
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with `upd_cs cs xs = []` have "cs = []" by fastforce 
      with `cs = c'#cs'` have False by simp
      thus ?thesis by simp
    next
      case (Cons x' xs')
      with `a#as = xs@ys` have "a = x'" and "as = xs'@ys" by simp_all
      with `upd_cs cs xs = []` Cons `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
      have "upd_cs cs' xs' = []" by simp
      from IH2[OF `as = xs'@ys` this] show ?thesis .
    qed
  }
qed


lemma slpa_number_Calls_eq_number_Returns:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; 
    \<forall>a \<in> set as. valid_edge a; \<forall>c \<in> set cs. valid_edge c\<rbrakk>
  \<Longrightarrow> length [a\<leftarrow>as@cs. \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs] = 
     length [a\<leftarrow>as. \<exists>Q p f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f]"
apply(induct rule:slpa_induct)
by(auto split:list.split edge_kind.split intro:only_call_get_return_edges 
         simp:intra_kind_def)


lemma slpa_get_proc:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; n -as\<rightarrow>* n'; 
    \<forall>c \<in> set cs. valid_edge c\<rbrakk>
  \<Longrightarrow> (if cs = [] then get_proc n else get_proc(last(sourcenodes cs))) = get_proc n'"
proof(induct arbitrary:n rule:slpa_induct)
  case slpa_empty thus ?case by fastforce
next
  case (slpa_intra cs a as)
  note IH = `\<And>n. \<lbrakk>upd_cs cs as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set cs. valid_edge a\<rbrakk>
    \<Longrightarrow> (if cs = [] then get_proc n else get_proc (last (sourcenodes cs))) = 
        get_proc n'`
  from `intra_kind (kind a)` `upd_cs cs (a#as) = []`
  have "upd_cs cs as = []" by(cases "kind a",auto simp:intra_kind_def)
  from `n -a#as\<rightarrow>* n'` have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "valid_edge a" and "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from `valid_edge a` `intra_kind (kind a)` ` n = sourcenode a`
  have "get_proc n = get_proc (targetnode a)"
    by(fastforce intro:get_proc_intra)
  from IH[OF `upd_cs cs as = []` `targetnode a -as\<rightarrow>* n'` `\<forall>a\<in>set cs. valid_edge a`]
  have "(if cs = [] then get_proc (targetnode a) 
         else get_proc (last (sourcenodes cs))) = get_proc n'" .
  with `get_proc n = get_proc (targetnode a)` show ?case by auto
next
  case (slpa_Call cs a as Q r p fs)
  note IH = `\<And>n. \<lbrakk>upd_cs (a#cs) as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set (a#cs). valid_edge a\<rbrakk>
    \<Longrightarrow> (if a#cs = [] then get_proc n else get_proc (last (sourcenodes (a#cs)))) = 
        get_proc n'`
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs cs (a#as) = []`
  have "upd_cs (a#cs) as = []" by simp
  from `n -a#as\<rightarrow>* n'` have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "valid_edge a" and "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from `valid_edge a` `\<forall>a\<in>set cs. valid_edge a` have "\<forall>a\<in>set (a#cs). valid_edge a"
    by simp
  from IH[OF `upd_cs (a#cs) as = []` `targetnode a -as\<rightarrow>* n'` this]
  have "get_proc (last (sourcenodes (a#cs))) = get_proc n'" by simp
  with `n = sourcenode a` show ?case by(cases cs,auto simp:sourcenodes_def)
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = `\<And>n. \<lbrakk>upd_cs cs' as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set cs'. valid_edge a\<rbrakk>
    \<Longrightarrow> (if cs' = [] then get_proc n else get_proc (last (sourcenodes cs'))) = 
       get_proc n'`
  from `\<forall>a\<in>set cs. valid_edge a` `cs = c'#cs'`
  have "valid_edge c'" and "\<forall>a\<in>set cs'. valid_edge a" by simp_all
  from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `upd_cs cs (a#as) = []` `cs = c'#cs'`
  have "upd_cs cs' as = []" by simp
  from `n -a#as\<rightarrow>* n'` have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from `valid_edge c'` `a \<in> get_return_edges c'`
  have "get_proc (sourcenode c') = get_proc (targetnode a)"
    by(rule get_proc_get_return_edge)
  from IH[OF `upd_cs cs' as = []` `targetnode a -as\<rightarrow>* n'` `\<forall>a\<in>set cs'. valid_edge a`]
  have "(if cs' = [] then get_proc (targetnode a) 
         else get_proc (last (sourcenodes cs'))) = get_proc n'" .
  with `cs = c'#cs'` `get_proc (sourcenode c') = get_proc (targetnode a)`
  show ?case by(auto simp:sourcenodes_def)
qed


lemma slpa_get_return_edges:
  "\<lbrakk>same_level_path_aux cs as; cs \<noteq> []; upd_cs cs as = [];
  \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<rbrakk>
  \<Longrightarrow> last as \<in> get_return_edges (last cs)"
proof(induct rule:slpa_induct)
  case (slpa_empty cs)
  from `cs \<noteq> []` `upd_cs cs [] = []` have False by fastforce
  thus ?case by simp
next
  case (slpa_intra cs a as)
  note IH = `\<lbrakk>cs \<noteq> []; upd_cs cs as = []; 
              \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last cs)`
  show ?case
  proof(cases "as = []")
    case True
    with `intra_kind (kind a)` `upd_cs cs (a#as) = []` have "cs = []"
      by(fastforce simp:intra_kind_def)
    with `cs \<noteq> []` have False by simp
    thus ?thesis by simp
  next
    case False
    from `intra_kind (kind a)` `upd_cs cs (a#as) = []` have "upd_cs cs as = []"
      by(fastforce simp:intra_kind_def)
    from `\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []` `intra_kind (kind a)`
    have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []"
      apply(clarsimp,erule_tac x="a#xs" in allE)
      by(auto simp:intra_kind_def)
    from IH[OF `cs \<noteq> []` `upd_cs cs as = []` this] 
    have "last as \<in> get_return_edges (last cs)" .
    with False show ?thesis by simp
  qed
next
  case (slpa_Call cs a as Q r p fs)
  note IH = `\<lbrakk>a#cs \<noteq> []; upd_cs (a#cs) as = [];
    \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs (a#cs) xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last (a#cs))`
  show ?case
  proof(cases "as = []")
    case True
    with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs cs (a#as) = []` have "a#cs = []" by simp
    thus ?thesis by simp
  next
    case False
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs cs (a#as) = []` have "upd_cs (a#cs) as = []"
      by simp
    from `\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs (a#cs) xs \<noteq> []"
      by(clarsimp,erule_tac x="a#xs" in allE,simp)
    from IH[OF _ `upd_cs (a#cs) as = []` this] 
    have "last as \<in> get_return_edges (last (a#cs))" by simp
    with False `cs \<noteq> []` show ?thesis by(simp add:targetnodes_def)
  qed
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = `\<lbrakk>cs' \<noteq> []; upd_cs cs' as = []; 
    \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs' xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last cs')`
  show ?case
  proof(cases "as = []")
    case True
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` `upd_cs cs (a#as) = []`
    have "cs' = []" by simp
    with `cs = c'#cs'` `a \<in> get_return_edges c'` True
    show ?thesis by simp
  next
    case False
    from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'` `upd_cs cs (a#as) = []`
    have "upd_cs cs' as = []" by simp
    show ?thesis
    proof(cases "cs' = []")
      case True
      with `cs = c'#cs'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "upd_cs cs [a] = []" by simp
      with `\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []` False have False
        apply(erule_tac x="[a]" in allE) by fastforce
      thus ?thesis by simp
    next
      case False
      from `\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []`
        `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
      have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs' xs \<noteq> []"
        by(clarsimp,erule_tac x="a#xs" in allE,simp)
      from IH[OF False `upd_cs cs' as = []` this]
      have "last as \<in> get_return_edges (last cs')" .
      with `as \<noteq> []` False `cs = c'#cs'` show ?thesis by(simp add:targetnodes_def)
    qed
  qed
qed


lemma slpa_callstack_length:
  assumes "same_level_path_aux cs as" and "length cs = length cfsx"
  obtains cfx cfsx' where "transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs"
  and "transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs'"
  and "length cfsx' = length (upd_cs cs as)"
proof(atomize_elim)
  from assms show "\<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
    transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
    length cfsx' = length (upd_cs cs as)"
  proof(induct arbitrary:cfsx cf rule:slpa_induct)
    case (slpa_empty cs) thus ?case by(simp add:kinds_def)
  next
    case (slpa_intra cs a as)
    note IH = `\<And>cfsx cf. length cs = length cfsx \<Longrightarrow>
      \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                  transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                  length cfsx' = length (upd_cs cs as)`
    from `intra_kind (kind a)` 
    have "length (upd_cs cs (a#as)) = length (upd_cs cs as)"
      by(fastforce simp:intra_kind_def)
    show ?case
    proof(cases cfsx)
      case Nil
      with `length cs = length cfsx` have "length cs = length []" by simp
      from Nil `intra_kind (kind a)` 
      obtain cfx where transfer:"transfer (kind a) (cfsx@cf#cfs) = []@cfx#cfs"
        "transfer (kind a) (cfsx@cf#cfs') = []@cfx#cfs'"
        by(cases "kind a",auto simp:kinds_def intra_kind_def)
      from IH[OF `length cs = length []`] obtain cfsx' cfx' 
        where "transfers (kinds as) ([]@cfx#cfs) = cfsx'@cfx'#cfs"
        and "transfers (kinds as) ([]@cfx#cfs') = cfsx'@cfx'#cfs'"
        and "length cfsx' = length (upd_cs cs as)" by blast
      with `length (upd_cs cs (a#as)) = length (upd_cs cs as)` transfer
      show ?thesis by(fastforce simp:kinds_def)
    next
      case (Cons x xs)
      with `intra_kind (kind a)` obtain cfx' 
        where transfer:"transfer (kind a) (cfsx@cf#cfs) = (cfx'#xs)@cf#cfs"
        "transfer (kind a) (cfsx@cf#cfs') = (cfx'#xs)@cf#cfs'"
        by(cases "kind a",auto simp:kinds_def intra_kind_def)
      from `length cs = length cfsx` Cons have "length cs = length (cfx'#xs)"
        by simp
      from IH[OF this] obtain cfs'' cf''
        where "transfers (kinds as) ((cfx'#xs)@cf#cfs) = cfs''@cf''#cfs"
        and "transfers (kinds as) ((cfx'#xs)@cf#cfs') = cfs''@cf''#cfs'"
        and "length cfs'' = length (upd_cs cs as)" by blast
      with `length (upd_cs cs (a#as)) = length (upd_cs cs as)` transfer
      show ?thesis by(fastforce simp:kinds_def)
    qed
  next
    case (slpa_Call cs a as Q r p fs)
    note IH = `\<And>cfsx cf. length (a#cs) = length cfsx \<Longrightarrow>
      \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                  transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                  length cfsx' = length (upd_cs (a#cs) as)`
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain cfx where transfer:"transfer (kind a) (cfsx@cf#cfs) = (cfx#cfsx)@cf#cfs"
      "transfer (kind a) (cfsx@cf#cfs') = (cfx#cfsx)@cf#cfs'"
      by(cases cfsx) auto
    from `length cs = length cfsx` have "length (a#cs) = length (cfx#cfsx)"
      by simp
    from IH[OF this] obtain cfsx' cfx' 
      where "transfers (kinds as) ((cfx#cfsx)@cf#cfs) = cfsx'@cfx'#cfs"
      and "transfers (kinds as) ((cfx#cfsx)@cf#cfs') = cfsx'@cfx'#cfs'"
      and "length cfsx' = length (upd_cs (a#cs) as)" by blast
    with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` transfer show ?case by(fastforce simp:kinds_def)
  next
     case (slpa_Return cs a as Q p f c' cs')
     note IH = `\<And>cfsx cf. length cs' = length cfsx \<Longrightarrow>
       \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                   transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                   length cfsx' = length (upd_cs cs' as)`
     from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c'#cs'`
     have "length (upd_cs cs (a#as)) = length (upd_cs cs' as)" by simp
     show ?case
     proof(cases cs')
       case Nil
       with `cs = c'#cs'` `length cs = length cfsx` obtain cfx
         where [simp]:"cfsx = [cfx]" by(cases cfsx) auto
       with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain cf' 
         where transfer:"transfer (kind a) (cfsx@cf#cfs) = []@cf'#cfs"
         "transfer (kind a) (cfsx@cf#cfs') = []@cf'#cfs'"
         by fastforce
       from Nil have "length cs' = length []" by simp
       from IH[OF this] obtain cfsx' cfx' 
         where "transfers (kinds as) ([]@cf'#cfs) = cfsx'@cfx'#cfs"
         and "transfers (kinds as) ([]@cf'#cfs') = cfsx'@cfx'#cfs'"
         and "length cfsx' = length (upd_cs cs' as)" by blast
       with `length (upd_cs cs (a#as)) = length (upd_cs cs' as)` transfer
       show ?thesis by(fastforce simp:kinds_def)
    next
      case (Cons cx csx)
      with `cs = c'#cs'` `length cs = length cfsx` obtain x x' xs
        where [simp]:"cfsx = x#x'#xs" and "length xs = length csx"
        by(cases cfsx,auto,case_tac list,fastforce+)
      with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain cf' 
        where transfer:"transfer (kind a) ((x#x'#xs)@cf#cfs) = (cf'#xs)@cf#cfs"
        "transfer (kind a) ((x#x'#xs)@cf#cfs') = (cf'#xs)@cf#cfs'"
        by fastforce
      from `cs = c'#cs'` `length cs = length cfsx` have "length cs' = length (cf'#xs)"
        by simp
      from IH[OF this] obtain cfsx' cfx 
        where "transfers (kinds as) ((cf'#xs)@cf#cfs) = cfsx'@cfx#cfs"
        and "transfers (kinds as) ((cf'#xs)@cf#cfs') = cfsx'@cfx#cfs'"
        and "length cfsx' = length (upd_cs cs' as)" by blast
      with `length (upd_cs cs (a#as)) = length (upd_cs cs' as)` transfer
      show ?thesis by(fastforce simp:kinds_def)
    qed
  qed
qed


lemma slpa_snoc_intra:
  "\<lbrakk>same_level_path_aux cs as; intra_kind (kind a)\<rbrakk> 
  \<Longrightarrow> same_level_path_aux cs (as@[a])"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma slpa_snoc_Call:
  "\<lbrakk>same_level_path_aux cs as; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs (as@[a])"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma vpa_Main_slpa:
  "\<lbrakk>valid_path_aux cs as; m -as\<rightarrow>* m'; as \<noteq> []; 
    valid_call_list cs m; get_proc m' = Main;
    get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = []"
proof(induct arbitrary:m rule:vpa_induct)
  case (vpa_empty cs) thus ?case by simp
next
  case (vpa_intra cs a as)
  note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list cs m; get_proc m' = Main;
    get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = []`
  from `m -a # as\<rightarrow>* m'` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from `valid_edge a` `intra_kind (kind a)` 
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  show ?case
  proof(cases "as = []")
    case True
    with `targetnode a -as\<rightarrow>* m'` have "targetnode a = m'" by fastforce
    with `get_proc (sourcenode a) = get_proc (targetnode a)` 
      `sourcenode a = m` `get_proc m' = Main`
    have "get_proc m = Main" by simp
    have "cs = []"
    proof(cases cs)
      case Cons
      with `valid_call_list cs m`
      obtain c Q r p fs where "valid_edge c" and "kind c = Q:r\<hookrightarrow>\<^bsub>get_proc m\<^esub>fs"
        by(auto simp:valid_call_list_def,erule_tac x="[]" in allE,
           auto simp:sourcenodes_def)
      with `get_proc m = Main` have "kind c = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by simp
      with `valid_edge c` have False by(rule Main_no_call_target)
      thus ?thesis by simp
    qed simp
    with True `intra_kind (kind a)` show ?thesis by(fastforce simp:intra_kind_def)
  next
    case False
    from `valid_call_list cs m` `sourcenode a = m`
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_call_list cs (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    from `get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main`
      `sourcenode a = m` `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "get_proc (case cs of [] \<Rightarrow> targetnode a | _ \<Rightarrow> sourcenode (last cs)) = Main"
      by(cases cs) auto
    from IH[OF `targetnode a -as\<rightarrow>* m'` False `valid_call_list cs (targetnode a)`
      `get_proc m' = Main` this]
    have "same_level_path_aux cs as \<and> upd_cs cs as = []" .
    with `intra_kind (kind a)` show ?thesis by(fastforce simp:intra_kind_def)
  qed
next
  case (vpa_Call cs a as Q r p fs)
  note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list (a # cs) m; 
    get_proc m' = Main; 
    get_proc (case a # cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last (a # cs))) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux (a # cs) as \<and> upd_cs (a # cs) as = []`
  from `m -a # as\<rightarrow>* m'` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  show ?case
  proof(cases "as = []")
    case True
    with `targetnode a -as\<rightarrow>* m'` have "targetnode a = m'" by fastforce
    with `get_proc (targetnode a) = p` `get_proc m' = Main` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by simp
    with `valid_edge a` have False by(rule Main_no_call_target)
    thus ?thesis by simp
  next
    case False
    from `get_proc (targetnode a) = p` `valid_call_list cs m` `valid_edge a`
      `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `sourcenode a = m`
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    from `get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main`
      `sourcenode a = m`
    have "get_proc (case a # cs of [] \<Rightarrow> targetnode a 
      | _ \<Rightarrow> sourcenode (last (a # cs))) = Main"
      by(cases cs) auto
    from IH[OF `targetnode a -as\<rightarrow>* m'` False `valid_call_list (a#cs) (targetnode a)`
      `get_proc m' = Main` this]
    have "same_level_path_aux (a # cs) as \<and> upd_cs (a # cs) as = []" .
    with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?thesis by simp
  qed
next
  case (vpa_ReturnEmpty cs a as Q p f)
  note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list [] m; get_proc m' = Main;
    get_proc (case [] of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last [])) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and> upd_cs [] as = []`
  from `m -a # as\<rightarrow>* m'` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p" 
    by(rule get_proc_return)
  from `get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main`
    `cs = []`
  have "get_proc m = Main" by simp
  with `sourcenode a = m` `get_proc (sourcenode a) = p` have "p = Main" by simp
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
  with `valid_edge a` have False by(rule Main_no_return_source)
  thus ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f c' cs')
  note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list cs' m; get_proc m' = Main;
    get_proc (case cs' of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs')) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux cs' as \<and> upd_cs cs' as = []`
  from `m -a # as\<rightarrow>* m'` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p" 
    by(rule get_proc_return)
  from `valid_call_list cs m` `cs = c' # cs'`
  have "valid_edge c'" 
    by(auto simp:valid_call_list_def,erule_tac x="[]" in allE,auto)
  from `valid_edge c'` `a \<in> get_return_edges c'`
  have "get_proc (sourcenode c') = get_proc (targetnode a)"
    by(rule get_proc_get_return_edge)
  show ?case
  proof(cases "as = []")
    case True
    with `targetnode a -as\<rightarrow>* m'` have "targetnode a = m'" by fastforce
    with `get_proc m' = Main` have "get_proc (targetnode a) = Main" by simp
    from `get_proc (sourcenode c') = get_proc (targetnode a)`
      `get_proc (targetnode a) = Main`
    have "get_proc (sourcenode c') = Main" by simp
    have "cs' = []"
    proof(cases cs')
      case (Cons cx csx)
      with `cs = c' # cs'` `valid_call_list cs m`
      obtain Qx rx fsx where "valid_edge cx" 
        and "kind cx = Qx:rx\<hookrightarrow>\<^bsub>get_proc (sourcenode c')\<^esub>fsx"
        by(auto simp:valid_call_list_def,erule_tac x="[c']" in allE,
           auto simp:sourcenodes_def)
      with `get_proc (sourcenode c') = Main` have "kind cx = Qx:rx\<hookrightarrow>\<^bsub>Main\<^esub>fsx" by simp
      with `valid_edge cx` have False by(rule Main_no_call_target)
      thus ?thesis by simp
    qed simp
    with True `cs = c' # cs'` `a \<in> get_return_edges c'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
    show ?thesis by simp
  next
    case False
    from `valid_call_list cs m` `cs = c' # cs'`
      `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(hypsubst_thin)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    from `get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main`
      `cs = c' # cs'` `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "get_proc (case cs' of [] \<Rightarrow> targetnode a 
      | _ \<Rightarrow> sourcenode (last cs')) = Main"
      by(cases cs') auto
    from IH[OF `targetnode a -as\<rightarrow>* m'` False `valid_call_list cs' (targetnode a)`
      `get_proc m' = Main` this]
    have "same_level_path_aux cs' as \<and> upd_cs cs' as = []" .
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c' # cs'` `a \<in> get_return_edges c'`
    show ?thesis by simp
  qed
qed



definition same_level_path :: "'edge list \<Rightarrow> bool"
  where "same_level_path as \<equiv> same_level_path_aux [] as \<and> upd_cs [] as = []"


lemma same_level_path_valid_path:
  "same_level_path as \<Longrightarrow> valid_path as"
by(fastforce intro:same_level_path_aux_valid_path_aux
             simp:same_level_path_def valid_path_def)


lemma same_level_path_Append:
  "\<lbrakk>same_level_path as; same_level_path as'\<rbrakk> \<Longrightarrow> same_level_path (as@as')"
by(fastforce elim:same_level_path_aux_Append upd_cs_Append simp:same_level_path_def)


lemma same_level_path_number_Calls_eq_number_Returns:
  "\<lbrakk>same_level_path as; \<forall>a \<in> set as. valid_edge a\<rbrakk> \<Longrightarrow> 
  length [a\<leftarrow>as. \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs] = length [a\<leftarrow>as. \<exists>Q p f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f]"
by(fastforce dest:slpa_number_Calls_eq_number_Returns simp:same_level_path_def)


lemma same_level_path_valid_path_Append:
  "\<lbrakk>same_level_path as; valid_path as'\<rbrakk> \<Longrightarrow> valid_path (as@as')"
  by(fastforce intro:valid_path_aux_Append elim:same_level_path_aux_valid_path_aux
               simp:valid_path_def same_level_path_def)

lemma valid_path_same_level_path_Append:
  "\<lbrakk>valid_path as; same_level_path as'\<rbrakk> \<Longrightarrow> valid_path (as@as')"
  apply(auto simp:valid_path_def same_level_path_def)
  apply(erule valid_path_aux_Append)
  by(fastforce intro!:same_level_path_aux_valid_path_aux 
                dest:same_level_path_aux_callstack_Append)

lemma intras_same_level_path:
  assumes "\<forall>a \<in> set as. intra_kind(kind a)" shows "same_level_path as"
proof -
  from `\<forall>a \<in> set as. intra_kind(kind a)` have "same_level_path_aux [] as"
    by(induct as)(auto simp:intra_kind_def)
  moreover
  from `\<forall>a \<in> set as. intra_kind(kind a)` have "upd_cs [] as = []"
    by(induct as)(auto simp:intra_kind_def)
  ultimately show ?thesis by(simp add:same_level_path_def)
qed


definition same_level_path' :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ -_\<rightarrow>\<^bsub>sl\<^esub>* _" [51,0,0] 80)
where slp_def:"n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<equiv> n -as\<rightarrow>* n' \<and> same_level_path as"

lemma slp_vp: "n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<Longrightarrow> n -as\<rightarrow>\<^sub>\<surd>* n'"
by(fastforce intro:same_level_path_valid_path simp:slp_def vp_def)


lemma intra_path_slp: "n -as\<rightarrow>\<^sub>\<iota>* n' \<Longrightarrow> n -as\<rightarrow>\<^bsub>sl\<^esub>* n'"
by(fastforce intro:intras_same_level_path simp:slp_def intra_path_def)


lemma slp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^bsub>sl\<^esub>* n''; n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^bsub>sl\<^esub>* n'"
  by(fastforce simp:slp_def intro:path_Append same_level_path_Append)


lemma slp_vp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^bsub>sl\<^esub>* n''; n'' -as'\<rightarrow>\<^sub>\<surd>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<surd>* n'"
  by(fastforce simp:slp_def vp_def intro:path_Append same_level_path_valid_path_Append)


lemma vp_slp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<surd>* n''; n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<surd>* n'"
  by(fastforce simp:slp_def vp_def intro:path_Append valid_path_same_level_path_Append)


lemma slp_get_proc:
  "n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<Longrightarrow> get_proc n = get_proc n'"
by(fastforce dest:slpa_get_proc simp:same_level_path_def slp_def)


lemma same_level_path_inner_path:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'"
  obtains as' where "n -as'\<rightarrow>\<^sub>\<iota>* n'" and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
proof(atomize_elim)
  from `n -as\<rightarrow>\<^bsub>sl\<^esub>* n'` have "n -as\<rightarrow>* n'" and "same_level_path as"
    by(simp_all add:slp_def)
  from `same_level_path as` have "same_level_path_aux [] as" and "upd_cs [] as = []"
    by(simp_all add:same_level_path_def)
  from `n -as\<rightarrow>* n'` `same_level_path_aux [] as` `upd_cs [] as = []`
  show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  proof(induct as arbitrary:n rule:length_induct)
    fix as n
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n''. n'' -as''\<rightarrow>* n' \<longrightarrow> same_level_path_aux [] as'' \<longrightarrow>
           upd_cs [] as'' = [] \<longrightarrow>
           (\<exists>as'. n'' -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as'')))"
      and "n -as\<rightarrow>* n'" and "same_level_path_aux [] as" and "upd_cs [] as = []"
    show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as)"
    proof(cases as)
      case Nil
      with `n -as\<rightarrow>* n'` show ?thesis by(fastforce simp:intra_path_def)
    next
      case (Cons a' as')
      with `n -as\<rightarrow>* n'` Cons have "n = sourcenode a'" and "valid_edge a'" 
        and "targetnode a' -as'\<rightarrow>* n'"
        by(auto intro:path_split_Cons)
      show ?thesis
      proof(cases "kind a'" rule:edge_kind_cases)
        case Intra
        with Cons `same_level_path_aux [] as` have "same_level_path_aux [] as'"
          by(fastforce simp:intra_kind_def)
        moreover
        from Intra Cons `upd_cs [] as = []` have "upd_cs [] as' = []"
          by(fastforce simp:intra_kind_def)
        ultimately obtain as'' where "targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'"
          and "set (sourcenodes as'') \<subseteq> set (sourcenodes as')"
          using IH Cons `targetnode a' -as'\<rightarrow>* n'`
          by(erule_tac x="as'" in allE) auto
        from `n = sourcenode a'` `valid_edge a'` Intra `targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'`
        have "n -a'#as''\<rightarrow>\<^sub>\<iota>* n'" by(fastforce intro:Cons_path simp:intra_path_def)
        with `set (sourcenodes as'') \<subseteq> set (sourcenodes as')` Cons show ?thesis
          by(rule_tac x="a'#as''" in exI,auto simp:sourcenodes_def)
      next
        case (Call Q p f)
        with Cons `same_level_path_aux [] as`
        have "same_level_path_aux [a'] as'" by simp
        from Call Cons `upd_cs [] as = []` have "upd_cs [a'] as' = []" by simp
        hence "as' \<noteq> []" by fastforce
        with `upd_cs [a'] as' = []` obtain xs ys where "as' = xs@ys" and "xs \<noteq> []"
        and "upd_cs [a'] xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []"
          by -(erule upd_cs_empty_split,auto)
        from `same_level_path_aux [a'] as'` `as' = xs@ys` `upd_cs [a'] xs = []`
        have "same_level_path_aux [a'] xs" and "same_level_path_aux [] ys"
          by(auto intro:slpa_split)
        from `same_level_path_aux [a'] xs` `upd_cs [a'] xs = []`
          `\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []`
        have "last xs \<in> get_return_edges (last [a'])"
          by(fastforce intro!:slpa_get_return_edges)
        with `valid_edge a'` Call
        obtain a where "valid_edge a" and "sourcenode a = sourcenode a'"
          and "targetnode a = targetnode (last xs)" and "kind a = (\<lambda>cf. False)\<^sub>\<surd>"
          by -(drule call_return_node_edge,auto)
        from `targetnode a = targetnode (last xs)` `xs \<noteq> []`
        have "targetnode a = targetnode (last (a'#xs))" by simp
        from `as' = xs@ys` `xs \<noteq> []` Cons have "length ys < length as" by simp
        from `targetnode a' -as'\<rightarrow>* n'` `as' = xs@ys` `xs \<noteq> []`
        have "targetnode (last (a'#xs)) -ys\<rightarrow>* n'"
          by(cases xs rule:rev_cases,auto dest:path_split)
        with IH `length ys < length as` `same_level_path_aux [] ys`
          `upd_cs [] ys = []`
        obtain as'' where "targetnode (last (a'#xs)) -as''\<rightarrow>\<^sub>\<iota>* n'"
          and "set(sourcenodes as'') \<subseteq> set(sourcenodes ys)"
          apply(erule_tac x="ys" in allE) apply clarsimp
          apply(erule_tac x="targetnode (last (a'#xs))" in allE) 
          by clarsimp
        from `sourcenode a = sourcenode a'` `n = sourcenode a'`
          `targetnode a = targetnode (last (a'#xs))` `valid_edge a`
          `kind a = (\<lambda>cf. False)\<^sub>\<surd>` `targetnode (last (a'#xs)) -as''\<rightarrow>\<^sub>\<iota>* n'`
        have "n -a#as''\<rightarrow>\<^sub>\<iota>* n'"
          by(fastforce intro:Cons_path simp:intra_path_def intra_kind_def)
        moreover
        from `set(sourcenodes as'') \<subseteq> set(sourcenodes ys)` Cons `as' = xs@ys`
          `sourcenode a = sourcenode a'`
        have "set(sourcenodes (a#as'')) \<subseteq> set(sourcenodes as)"
          by(auto simp:sourcenodes_def)
        ultimately show ?thesis by blast
      next
        case (Return Q p f)
        with Cons `same_level_path_aux [] as` have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


lemma slp_callstack_length_equal:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'" obtains cf' where "transfers (kinds as) (cf#cfs) = cf'#cfs"
  and "transfers (kinds as) (cf#cfs') = cf'#cfs'"
proof(atomize_elim)
  from `n -as\<rightarrow>\<^bsub>sl\<^esub>* n'` have "same_level_path_aux [] as" and "upd_cs [] as = []"
    by(simp_all add:slp_def same_level_path_def)
  then obtain cfx cfsx where "transfers (kinds as) (cf#cfs) = cfsx@cfx#cfs"
    and "transfers (kinds as) (cf#cfs') = cfsx@cfx#cfs'"
    and "length cfsx = length (upd_cs [] as)"
    by(fastforce elim:slpa_callstack_length)
  with `upd_cs [] as = []` have "cfsx = []" by(cases cfsx) auto
  with `transfers (kinds as) (cf#cfs) = cfsx@cfx#cfs`
    `transfers (kinds as) (cf#cfs') = cfsx@cfx#cfs'`
  show "\<exists>cf'. transfers (kinds as) (cf#cfs) = cf'#cfs \<and> 
    transfers (kinds as) (cf#cfs') = cf'#cfs'" by fastforce
qed


lemma slp_cases [consumes 1,case_names intra_path return_intra_path]:
  assumes "m -as\<rightarrow>\<^bsub>sl\<^esub>* m'"
  obtains "m -as\<rightarrow>\<^sub>\<iota>* m'"
  | as' a as'' Q p f where "as = as'@a#as''" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  and "m -as'@[a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a" and "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m'"
proof(atomize_elim)
  from `m -as\<rightarrow>\<^bsub>sl\<^esub>* m'` have "m -as\<rightarrow>* m'" and "same_level_path_aux [] as"
    and "upd_cs [] as = []" by(simp_all add:slp_def same_level_path_def)
  from `m -as\<rightarrow>* m'` have "\<forall>a \<in> set as. valid_edge a" by(rule path_valid_edges)
  have "\<forall>a \<in> set []. valid_edge a" by simp
  with `same_level_path_aux [] as` `upd_cs [] as = []` `\<forall>a \<in> set []. valid_edge a`
    `\<forall>a \<in> set as. valid_edge a`
  show "m -as\<rightarrow>\<^sub>\<iota>* m' \<or>
    (\<exists>as' a as'' Q p f. as = as' @ a # as'' \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and>
    m -as' @ [a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* m')"
  proof(cases rule:slpa_cases)
    case intra_path
    with `m -as\<rightarrow>* m'` have "m -as\<rightarrow>\<^sub>\<iota>* m'" by(simp add:intra_path_def)
    thus ?thesis by blast
  next
    case (return_intra_path as' a as'' Q p f c' cs')
    from `m -as\<rightarrow>* m'` `as = as' @ a # as''`
    have "m -as'\<rightarrow>* sourcenode a" and "valid_edge a" and "targetnode a -as''\<rightarrow>* m'"
      by(auto intro:path_split)
    from `m -as'\<rightarrow>* sourcenode a` `valid_edge a`
    have "m -as'@[a]\<rightarrow>* targetnode a" by(fastforce intro:path_Append path_edge)
    with `same_level_path_aux [] as'` `upd_cs [] as' = c' # cs'` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      `a \<in> get_return_edges c'`
    have "same_level_path_aux [] (as'@[a])"
      by(fastforce intro:same_level_path_aux_Append)
    with `upd_cs [] (as' @ [a]) = []` `m -as'@[a]\<rightarrow>* targetnode a`
    have "m -as'@[a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a" by(simp add:slp_def same_level_path_def)
    moreover
    from `\<forall>a\<in>set as''. intra_kind (kind a)` `targetnode a -as''\<rightarrow>* m'`
    have "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m'" by(simp add:intra_path_def)
    ultimately show ?thesis using `as = as' @ a # as''` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` by blast
  qed
qed


function same_level_path_rev_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "same_level_path_rev_aux cs [] \<longleftrightarrow> True"
  | "same_level_path_rev_aux cs (as@[a]) \<longleftrightarrow> 
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> same_level_path_rev_aux (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> False
                                     | c'#cs' \<Rightarrow> c' \<in> get_return_edges a \<and>
                                             same_level_path_rev_aux cs' as
                       |    _ \<Rightarrow> same_level_path_rev_aux cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order


lemma slpra_induct [consumes 1,case_names slpra_empty slpra_intra slpra_Return
  slpra_Call]:
  assumes major: "same_level_path_rev_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); same_level_path_rev_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; same_level_path_rev_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs c' cs'. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = c'#cs'; 
                   same_level_path_rev_aux cs' as; c' \<in> get_return_edges a; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (as@[a])"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs rule:rev_induct)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma same_level_path_rev_aux_Append:
  "\<lbrakk>same_level_path_rev_aux cs as'; same_level_path_rev_aux (upd_rev_cs cs as') as\<rbrakk>
  \<Longrightarrow> same_level_path_rev_aux cs (as@as')"
by(induct rule:slpra_induct,
   auto simp:intra_kind_def simp del:append_assoc simp:append_assoc[THEN sym])


lemma slpra_to_slpa:
  "\<lbrakk>same_level_path_rev_aux cs as; upd_rev_cs cs as = []; n -as\<rightarrow>* n'; 
  valid_return_list cs n'\<rbrakk>
  \<Longrightarrow> same_level_path_aux [] as \<and> same_level_path_aux (upd_cs [] as) cs \<and>
     upd_cs (upd_cs [] as) cs = []"
proof(induct arbitrary:n' rule:slpra_induct)
  case slpra_empty thus ?case by simp
next
  case (slpra_intra cs a as)
  note IH = `\<And>n'. \<lbrakk>upd_rev_cs cs as = []; n -as\<rightarrow>* n'; valid_return_list cs n'\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and> same_level_path_aux (upd_cs [] as) cs \<and>
       upd_cs (upd_cs [] as) cs = []`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)"
    by(rule get_proc_intra)
  with `valid_return_list cs n'` `n' = targetnode a`
  have "valid_return_list cs (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs')(auto simp:targetnodes_def)
  from `upd_rev_cs cs (as@[a]) = []` `intra_kind (kind a)`
  have "upd_rev_cs cs as = []" by(fastforce simp:intra_kind_def)
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  from IH[OF `upd_rev_cs cs as = []` `n -as\<rightarrow>* sourcenode a`
    `valid_return_list cs (sourcenode a)`]
  have "same_level_path_aux [] as" 
    and "same_level_path_aux (upd_cs [] as) cs"
    and "upd_cs (upd_cs [] as) cs = []" by simp_all
  from `same_level_path_aux [] as` `intra_kind (kind a)`
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_intra)
  from `intra_kind (kind a)`
  have "upd_cs [] (as@[a]) = upd_cs [] as"
    by(fastforce simp:upd_cs_Append intra_kind_def)
  moreover
  from `same_level_path_aux [] as` `intra_kind (kind a)`
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_intra)
  ultimately show ?case using `same_level_path_aux (upd_cs [] as) cs`
    `upd_cs (upd_cs [] as) cs = []`
    by simp
next
  case (slpra_Return cs a as Q p f)
  note IH = `\<And>n' n''. \<lbrakk>upd_rev_cs (a#cs) as = []; n -as\<rightarrow>* n';
    valid_return_list (a#cs) n'\<rbrakk>
  \<Longrightarrow> same_level_path_aux [] as \<and>
     same_level_path_aux (upd_cs [] as) (a#cs) \<and>
     upd_cs (upd_cs [] as) (a#cs) = []`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "p = get_proc (sourcenode a)"
     by(rule get_proc_return[THEN sym])
   from `valid_return_list cs n'` `n' = targetnode a`
   have "valid_return_list cs (targetnode a)" by simp
   with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `p = get_proc (sourcenode a)`
   have "valid_return_list (a#cs) (sourcenode a)"
     apply(clarsimp simp:valid_return_list_def)
     apply(case_tac cs') apply auto
     apply(erule_tac x="list" in allE) apply clarsimp
     by(case_tac list,auto simp:targetnodes_def)
   from `upd_rev_cs cs (as@[a]) = []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
   have "upd_rev_cs (a#cs) as = []" by simp
   from IH[OF this `n -as\<rightarrow>* sourcenode a` `valid_return_list (a#cs) (sourcenode a)`]
   have "same_level_path_aux [] as"
     and "same_level_path_aux (upd_cs [] as) (a#cs)"
     and "upd_cs (upd_cs [] as) (a#cs) = []" by simp_all
   show ?case 
  proof(cases "upd_cs [] as")
    case Nil
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `same_level_path_aux (upd_cs [] as) (a#cs)`
    have False by simp
    thus ?thesis by simp
  next
    case (Cons cx csx)
    with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `same_level_path_aux (upd_cs [] as) (a#cs)`
    obtain Qx fx 
      where match:"a \<in> get_return_edges cx" "same_level_path_aux csx cs" by auto
    from `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` Cons have "upd_cs [] (as@[a]) = csx"
      by(rule upd_cs_snoc_Return_Cons)
    with `same_level_path_aux (upd_cs [] as) (a#cs)`
      `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` match
    have "same_level_path_aux (upd_cs [] (as@[a])) cs" by simp
    from `upd_cs [] (as@[a]) = csx` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` Cons
      `upd_cs (upd_cs [] as) (a#cs) = []`
    have "upd_cs (upd_cs [] (as@[a])) cs = []" by simp
    from Cons `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` match
    have "same_level_path_aux (upd_cs [] as) [a]" by simp
    with `same_level_path_aux [] as` have "same_level_path_aux [] (as@[a])"
      by(rule same_level_path_aux_Append)
    with `same_level_path_aux (upd_cs [] (as@[a])) cs`
      `upd_cs (upd_cs [] (as@[a])) cs = []`
    show ?thesis by simp
  qed
next
  case (slpra_Call cs a as Q r p fs cx csx)
  note IH = `\<And>n'. \<lbrakk>upd_rev_cs csx as = []; n -as\<rightarrow>* n'; valid_return_list csx n'\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and>
       same_level_path_aux (upd_cs [] as) csx \<and> upd_cs (upd_cs [] as) csx = []`
  note match = `cs = cx#csx` `cx \<in> get_return_edges a`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from `valid_edge a` match 
  have "get_proc (sourcenode a) = get_proc (targetnode cx)"
    by(fastforce intro:get_proc_get_return_edge)
  with `valid_return_list cs n'` `cs = cx#csx`
  have "valid_return_list csx (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cx#cs'" in allE) apply clarsimp
    by(case_tac cs',auto simp:targetnodes_def)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` match `upd_rev_cs cs (as@[a]) = []`
  have "upd_rev_cs csx as = []" by simp
  from IH[OF this `n -as\<rightarrow>* sourcenode a` `valid_return_list csx (sourcenode a)`]
  have "same_level_path_aux [] as"
    and "same_level_path_aux (upd_cs [] as) csx" and "upd_cs (upd_cs [] as) csx = []"
    by simp_all
  from `same_level_path_aux [] as` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_Call)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` match obtain Q' f' where "kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs [] (as@[a]) = a#(upd_cs [] as)"
    by(rule upd_cs_snoc_Call)
  with `same_level_path_aux (upd_cs [] as) csx` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    `kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` match
  have "same_level_path_aux (upd_cs [] (as@[a])) cs" by simp
  from `upd_cs (upd_cs [] as) csx = []` `upd_cs [] (as@[a]) = a#(upd_cs [] as)`
    `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` match
  have "upd_cs (upd_cs [] (as@[a])) cs = []" by simp
  with `same_level_path_aux [] (as@[a])`
    `same_level_path_aux (upd_cs [] (as@[a])) cs` show ?case by simp
qed


subsubsection {* Lemmas on paths with @{text "(_Entry_)"} *}

lemma path_Entry_target [dest]:
  assumes "n -as\<rightarrow>* (_Entry_)"
  shows "n = (_Entry_)" and "as = []"
using `n -as\<rightarrow>* (_Entry_)`
proof(induct n as n'\<equiv>"(_Entry_)" rule:path.induct)
  case (Cons_path n'' as a n)
  from `n'' = (_Entry_)` `targetnode a = n''` `valid_edge a` have False
    by -(rule Entry_target,simp_all)
  { case 1
    from `False` show ?case ..
  next
    case 2
    from `False` show ?case ..
  }
qed simp_all



lemma Entry_sourcenode_hd:
  assumes "n -as\<rightarrow>* n'" and "(_Entry_) \<in> set (sourcenodes as)"
  shows "n = (_Entry_)" and "(_Entry_) \<notin> set (sourcenodes (tl as))"
  using `n -as\<rightarrow>* n'` `(_Entry_) \<in> set (sourcenodes as)`
proof(induct rule:path.induct)
  case (empty_path n) case 1
  thus ?case by(simp add:sourcenodes_def)
next
  case (empty_path n) case 2
  thus ?case by(simp add:sourcenodes_def)
next
  case (Cons_path n'' as n' a n)
  note IH1 = `(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> n'' = (_Entry_)`
  note IH2 = `(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> (_Entry_) \<notin> set(sourcenodes(tl as))`
  have "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))"
  proof(rule ccontr)
    assume "\<not> (_Entry_) \<notin> set (sourcenodes (tl (a#as)))"
    hence "(_Entry_) \<in> set (sourcenodes as)" by simp
    from IH1[OF this] have "n'' = (_Entry_)" by simp
    with `targetnode a = n''` `valid_edge a` show False by -(erule Entry_target,simp)
  qed
  hence "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))" by fastforce
  { case 1
    with `(_Entry_) \<notin> set (sourcenodes(tl(a#as)))` `sourcenode a = n`
    show ?case by(simp add:sourcenodes_def)
  next
    case 2
    with `(_Entry_) \<notin> set (sourcenodes(tl(a#as)))` `sourcenode a = n`
    show ?case by(simp add:sourcenodes_def)
  }
qed


lemma Entry_no_inner_return_path: 
  assumes "(_Entry_) -as@[a]\<rightarrow>* n" and "\<forall>a \<in> set as. intra_kind(kind a)"
  and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "False"
proof -
  from `(_Entry_) -as@[a]\<rightarrow>* n` have "(_Entry_) -as\<rightarrow>* sourcenode a" 
    and "valid_edge a" and "targetnode a = n" by(auto intro:path_split_snoc)
  from `(_Entry_) -as\<rightarrow>* sourcenode a` `\<forall>a \<in> set as. intra_kind(kind a)`
  have "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* sourcenode a" by(simp add:intra_path_def)
  hence "get_proc (sourcenode a) = Main"
    by(fastforce dest:intra_path_get_procs simp:get_proc_Entry)
  with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "p = Main"
    by(fastforce dest:get_proc_return)
  with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show ?thesis
    by(fastforce intro:Main_no_return_source)
qed



lemma vpra_no_slpra:
  "\<lbrakk>valid_path_rev_aux cs as; n -as\<rightarrow>* n'; valid_return_list cs n'; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> (\<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> [])\<rbrakk>
  \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f"
proof(induct arbitrary:n' rule:vpra_induct)
  case (vpra_empty cs)
  from `valid_return_list cs n'` `cs \<noteq> []` obtain Q f where "valid_edge (hd cs)"
    and "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f"
    apply(unfold valid_return_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from `n -[]\<rightarrow>* n'` have "n = n'" by fastforce
  with `valid_edge (hd cs)` `kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f` show ?case by blast
next
  case (vpra_intra cs a as)
  note IH = `\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list cs n'; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f`
  note all = `\<forall>xs ys. as@[a] = xs@ys 
    \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from `valid_return_list cs n'` `cs \<noteq> []` obtain Q f where "valid_edge (hd cs)"
    and "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f"
    apply(unfold valid_return_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with `kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f` `targetnode a = n'`
  have "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc (sourcenode a)\<^esub>f" by simp
  from `valid_return_list cs n'` `targetnode a = n'`
    `get_proc (sourcenode a) = get_proc (targetnode a)`
  have "valid_return_list cs (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
  from all `intra_kind (kind a)`
  have "\<forall>xs ys. as = xs@ys 
    \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []"
    apply clarsimp apply(erule_tac x="xs" in allE)
    by(auto simp:intra_kind_def)
  from IH[OF `n -as\<rightarrow>* sourcenode a` `valid_return_list cs (sourcenode a)`
    `cs \<noteq> []` this] show ?case .
next
  case (vpra_Return cs a as Q p f)
  note IH = `\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list (a#cs) n'; a#cs \<noteq> [];
   \<forall>xs ys. as = xs @ ys \<longrightarrow>
    \<not> same_level_path_rev_aux (a#cs) ys \<or> upd_rev_cs (a#cs) ys \<noteq> []\<rbrakk>
  \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p"
    by(rule get_proc_return)
  with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `valid_return_list cs n'` `valid_edge a` `targetnode a = n'`
  have "valid_return_list (a#cs) (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split simp:targetnodes_def)
  from `\<forall>xs ys. as@[a] = xs@ys \<longrightarrow>
    \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
  have "\<forall>xs ys. as = xs@ys \<longrightarrow>
    \<not> same_level_path_rev_aux (a#cs) ys \<or> upd_rev_cs (a#cs) ys \<noteq> []"
    apply clarsimp apply(erule_tac x="xs" in allE)
    by auto
  from IH[OF `n -as\<rightarrow>* sourcenode a` `valid_return_list (a#cs) (sourcenode a)`
    _ this] show ?case by simp
next
  case (vpra_CallEmpty cs a as Q p fs)
  from `cs = []` `cs \<noteq> []` have False by simp
  thus ?case by simp
next
  case (vpra_CallCons cs a as Q r p fs c' cs')
  note IH = `\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list cs' n'; cs' \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow>
       \<not> same_level_path_rev_aux cs' ys \<or> upd_rev_cs cs' ys \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f`
  note all = `\<forall>xs ys. as@[a] = xs@ys \<longrightarrow>
     \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []`
  from `n -as@[a]\<rightarrow>* n'` have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from `valid_return_list cs n'` `cs = c'#cs'` have "valid_edge c'"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="[]" in allE)
    by auto
  show ?case
  proof(cases "cs' = []")
    case True
    with `cs = c'#cs'` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `c' \<in> get_return_edges a`
    have "same_level_path_rev_aux cs ([]@[a])"
      and "upd_rev_cs cs ([]@[a]) = []"
      by(simp only:same_level_path_rev_aux.simps upd_rev_cs.simps,clarsimp)+
    with all have False by(erule_tac x="as" in allE) fastforce
    thus ?thesis by simp
  next
    case False
    with `valid_return_list cs n'` `cs = c'#cs'`
    have "valid_return_list cs' (targetnode c')"
      apply(clarsimp simp:valid_return_list_def)
      apply(hypsubst_thin)
      apply(erule_tac x="c'#cs'" in allE)
      apply(auto simp:targetnodes_def)
       apply(case_tac cs') apply auto
      apply(case_tac list) apply(auto simp:targetnodes_def)
      done
    from `valid_edge a` `c' \<in> get_return_edges a`
    have "get_proc (sourcenode a) = get_proc (targetnode c')"
      by(rule get_proc_get_return_edge)
    with `valid_return_list cs' (targetnode c')`
    have "valid_return_list cs' (sourcenode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(hypsubst_thin)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
    from all `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `cs = c'#cs'` `c' \<in> get_return_edges a`
    have "\<forall>xs ys. as = xs@ys 
      \<longrightarrow> \<not> same_level_path_rev_aux cs' ys \<or> upd_rev_cs cs' ys \<noteq> []"
      apply clarsimp apply(erule_tac x="xs" in allE)
      by auto  
    from IH[OF `n -as\<rightarrow>* sourcenode a` `valid_return_list cs' (sourcenode a)`
      False this] show ?thesis .
  qed
qed


lemma valid_Entry_path_cases:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n" and "as \<noteq> []"
  shows "(\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n)"
proof -
  from `as \<noteq> []` obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  thus ?thesis
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra with `as = as'@[a']` show ?thesis by simp
  next
    case Call with `as = as'@[a']` show ?thesis by simp
  next
    case (Return Q p f)
    from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` have "(_Entry_) -as\<rightarrow>* n" and "valid_path_rev_aux [] as"
      by(auto intro:vp_to_vpra simp:vp_def valid_path_def)
    from `(_Entry_) -as\<rightarrow>* n` `as = as'@[a']`
    have "(_Entry_) -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" 
      and "targetnode a' = n"
      by(auto intro:path_split_snoc)
    from `valid_path_rev_aux [] as` `as = as'@[a']` Return
    have "valid_path_rev_aux [a'] as'" by simp
    from `valid_edge a'` Return
    have "valid_return_list [a'] (sourcenode a')"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') 
      by(auto intro:get_proc_return[THEN sym])
    show ?thesis
    proof(cases "\<forall>xs ys. as' = xs@ys \<longrightarrow> 
        (\<not> same_level_path_rev_aux [a'] ys \<or> upd_rev_cs [a'] ys \<noteq> [])")
      case True
      with `valid_path_rev_aux [a'] as'` `(_Entry_) -as'\<rightarrow>* sourcenode a'`
        `valid_return_list [a'] (sourcenode a')`
      obtain ax Qx fx where "valid_edge ax" and "kind ax = Qx\<hookleftarrow>\<^bsub>get_proc (_Entry_)\<^esub>fx"
        by(fastforce dest!:vpra_no_slpra)
      hence False by(fastforce intro:Main_no_return_source simp:get_proc_Entry)
      thus ?thesis by simp
    next
      case False
      then obtain xs ys where "as' = xs@ys" and "same_level_path_rev_aux [a'] ys"
        and "upd_rev_cs [a'] ys = []" by auto
      with Return have "same_level_path_rev_aux [] (ys@[a'])"
        and "upd_rev_cs [] (ys@[a']) = []" by simp_all
      from `upd_rev_cs [a'] ys = []` have "ys \<noteq> []" by auto
      with `(_Entry_) -as'\<rightarrow>* sourcenode a'` `as' = xs@ys`
      have "hd(sourcenodes ys) -ys\<rightarrow>* sourcenode a'"
        by(cases ys)(auto dest:path_split_second simp:sourcenodes_def)
      with `targetnode a' = n` `valid_edge a'`
      have "hd(sourcenodes ys) -ys@[a']\<rightarrow>* n"
        by(fastforce intro:path_Append path_edge)
      with `same_level_path_rev_aux [] (ys@[a'])` `upd_rev_cs [] (ys@[a']) = []`
      have "same_level_path (ys@[a'])"
        by(fastforce dest:slpra_to_slpa simp:same_level_path_def valid_return_list_def)
      with `hd(sourcenodes ys) -ys@[a']\<rightarrow>* n` have "hd(sourcenodes ys) -ys@[a']\<rightarrow>\<^bsub>sl\<^esub>* n"
        by(simp add:slp_def)
      with `as = as'@[a']` `as' = xs@ys` Return
      have "\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n"
        by(rule_tac x="xs" in exI) auto
      thus ?thesis by simp
    qed
  qed
qed


lemma valid_Entry_path_ascending_path:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n"
  obtains as' where "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n" 
  and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
proof(atomize_elim)
  from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n`
  show "\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))"
  proof(induct as arbitrary:n rule:length_induct)
    fix as n
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n'. (_Entry_) -as''\<rightarrow>\<^sub>\<surd>* n' \<longrightarrow>
       (\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as'') \<and>
              (\<forall>a'\<in>set as'. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))))"
      and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n"
    show "\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))"
    proof(cases "as = []")
      case True
      with `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` show ?thesis by(fastforce simp:sourcenodes_def vp_def)
    next
      case False
      with `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n`
      have "((\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n)"
        by(fastforce dest!:valid_Entry_path_cases)
      thus ?thesis apply -
      proof(erule disjE)+
        assume "\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')"
        then obtain a' as' where "as = as'@[a']" and "intra_kind(kind a')" by blast
        from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` `as = as'@[a']`
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" and "valid_edge a'"
          and "targetnode a' = n"
          by(auto intro:vp_split_snoc)
        from `valid_edge a'` `intra_kind(kind a')`
        have "sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'"
          by(fastforce intro:path_edge intras_same_level_path simp:slp_def)
        from IH `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'` `as = as'@[a']`
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from `(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'` `sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'`
        have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* targetnode a'" by(rule vp_slp_Append)
        with `targetnode a' = n` have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* n" by simp
        moreover
        from `set (sourcenodes xs) \<subseteq> set (sourcenodes as')` `as = as'@[a']`
        have "set (sourcenodes (xs@[a'])) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from `\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)` 
          `intra_kind(kind a')`
        have "\<forall>a'\<in>set (xs@[a']). intra_kind (kind a') \<or> 
                                 (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
        then obtain a' as' Q r p fs where "as = as'@[a']" and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          by blast
        from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` `as = as'@[a']`
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" and "valid_edge a'"
          and "targetnode a' = n"
          by(auto intro:vp_split_snoc)
        from IH `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'` `as = as'@[a']`
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from `targetnode a' = n` `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          `(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'`
        have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* n"
          by(fastforce intro:path_Append path_edge vpa_snoc_Call 
                       simp:vp_def valid_path_def)
        moreover
        from `set (sourcenodes xs) \<subseteq> set (sourcenodes as')` `as = as'@[a']`
        have "set (sourcenodes (xs@[a'])) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from `\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)` 
          `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        have "\<forall>a'\<in>set (xs@[a']). intra_kind (kind a') \<or> 
                                 (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n"
        then obtain as' as'' n' where "as = as'@as''" and "as'' \<noteq> []"
          and "n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n" by blast
        from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n` `as = as'@as''` `as'' \<noteq> []`
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* hd(sourcenodes as'')"
          by(cases as'',auto intro:vp_split simp:sourcenodes_def)
        from `n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n` `as'' \<noteq> []` have "hd(sourcenodes as'') = n'"
          by(fastforce intro:path_sourcenode simp:slp_def)
        from `as = as'@as''` `as'' \<noteq> []` have "length as' < length as" by simp
        with IH `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* hd(sourcenodes as'')`
          `hd(sourcenodes as'') = n'`
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* n'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from `n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n` obtain ys where "n' -ys\<rightarrow>\<^sub>\<iota>* n"
          and "set(sourcenodes ys) \<subseteq> set(sourcenodes as'')"
          by(erule same_level_path_inner_path)
        from `(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* n'` `n' -ys\<rightarrow>\<^sub>\<iota>* n` have "(_Entry_) -xs@ys\<rightarrow>\<^sub>\<surd>* n"
          by(fastforce intro:vp_slp_Append intra_path_slp)
        moreover
        from `set (sourcenodes xs) \<subseteq> set (sourcenodes as')`
          `set(sourcenodes ys) \<subseteq> set(sourcenodes as'')` `as = as'@as''`
        have "set (sourcenodes (xs@ys)) \<subseteq> set(sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from `\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
          `n' -ys\<rightarrow>\<^sub>\<iota>* n`
        have "\<forall>a'\<in>set (xs@ys). intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by(fastforce simp:intra_path_def)
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed



end

end