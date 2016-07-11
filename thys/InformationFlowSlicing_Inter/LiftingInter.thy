section {* Framework Graph Lifting for Noninterference *}

theory LiftingInter 
imports NonInterferenceInter 
begin

text {* In this section, we show how a valid CFG from the slicing framework in
\cite{Wasserrab:08} can be lifted to fulfil all properties of the 
@{text "NonInterferenceIntraGraph"} locale. Basically, we redefine the
hitherto existing @{text Entry} and @{text Exit} nodes as new
@{text High} and @{text Low} nodes, and introduce two new nodes
@{text NewEntry} and @{text NewExit}. Then, we have to lift all functions
to operate on this new graph. *}

subsection {* Liftings *}

subsubsection {* The datatypes *}

datatype 'node LDCFG_node = Node 'node
  | NewEntry
  | NewExit


type_synonym ('edge,'node,'var,'val,'ret,'pname) LDCFG_edge = 
  "'node LDCFG_node \<times> (('var,'val,'ret,'pname) edge_kind) \<times> 'node LDCFG_node"


subsubsection {* Lifting basic definitions using @{typ 'edge} and @{typ 'node} *}

inductive lift_valid_edge :: "('edge \<Rightarrow> bool) \<Rightarrow> ('edge \<Rightarrow> 'node) \<Rightarrow> ('edge \<Rightarrow> 'node) \<Rightarrow>
  ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> 
  ('edge,'node,'var,'val,'ret,'pname) LDCFG_edge \<Rightarrow> 
  bool"
for valid_edge::"'edge \<Rightarrow> bool" and src::"'edge \<Rightarrow> 'node" and trg::"'edge \<Rightarrow> 'node" 
  and knd::"'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" and E::'node and X::'node

where lve_edge:
  "\<lbrakk>valid_edge a; src a \<noteq> E \<or> trg a \<noteq> X; 
    e = (Node (src a),knd a,Node (trg a))\<rbrakk>
  \<Longrightarrow> lift_valid_edge valid_edge src trg knd E X e"

  | lve_Entry_edge:
  "e = (NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node E) 
  \<Longrightarrow> lift_valid_edge valid_edge src trg knd E X e"

  | lve_Exit_edge:
  "e = (Node X,(\<lambda>s. True)\<^sub>\<surd>,NewExit) 
  \<Longrightarrow> lift_valid_edge valid_edge src trg knd E X e"

  | lve_Entry_Exit_edge:
  "e = (NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit) 
  \<Longrightarrow> lift_valid_edge valid_edge src trg knd E X e"


lemma [simp]:"\<not> lift_valid_edge valid_edge src trg knd E X (Node E,et,Node X)"
by(auto elim:lift_valid_edge.cases)



fun lift_get_proc :: "('node \<Rightarrow> 'pname) \<Rightarrow> 'pname \<Rightarrow> 'node LDCFG_node \<Rightarrow> 'pname"
  where "lift_get_proc get_proc Main (Node n) = get_proc n"
  | "lift_get_proc get_proc Main NewEntry = Main"
  | "lift_get_proc get_proc Main NewExit = Main"


inductive_set lift_get_return_edges :: "('edge \<Rightarrow> 'edge set) \<Rightarrow> ('edge \<Rightarrow> bool) \<Rightarrow> 
  ('edge \<Rightarrow> 'node) \<Rightarrow> ('edge \<Rightarrow> 'node) \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) 
  \<Rightarrow> ('edge,'node,'var,'val,'ret,'pname) LDCFG_edge 
  \<Rightarrow> ('edge,'node,'var,'val,'ret,'pname) LDCFG_edge set"
for get_return_edges :: "'edge \<Rightarrow> 'edge set" and valid_edge :: "'edge \<Rightarrow> bool"
  and src::"'edge \<Rightarrow> 'node" and trg::"'edge \<Rightarrow> 'node" 
  and knd::"'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and e::"('edge,'node,'var,'val,'ret,'pname) LDCFG_edge"
where lift_get_return_edgesI:
  "\<lbrakk>e = (Node (src a),knd a,Node (trg a)); valid_edge a; a' \<in> get_return_edges a; 
  e' = (Node (src a'),knd a',Node (trg a'))\<rbrakk>
  \<Longrightarrow> e' \<in> lift_get_return_edges get_return_edges valid_edge src trg knd e"


subsubsection {* Lifting the Def and Use sets *}

inductive_set lift_Def_set :: "('node \<Rightarrow> 'var set) \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> 
                       'var set \<Rightarrow> 'var set \<Rightarrow> ('node LDCFG_node \<times> 'var) set"
for Def::"('node \<Rightarrow> 'var set)" and E::'node and X::'node 
  and H::"'var set" and L::"'var set"

where lift_Def_node: 
  "V \<in> Def n \<Longrightarrow> (Node n,V) \<in> lift_Def_set Def E X H L"

  | lift_Def_High:
  "V \<in> H \<Longrightarrow> (Node E,V) \<in> lift_Def_set Def E X H L"

abbreviation lift_Def :: "('node \<Rightarrow> 'var set) \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> 
                       'var set \<Rightarrow> 'var set \<Rightarrow> 'node LDCFG_node \<Rightarrow> 'var set"
  where "lift_Def Def E X H L n \<equiv> {V. (n,V) \<in> lift_Def_set Def E X H L}"


inductive_set lift_Use_set :: "('node \<Rightarrow> 'var set) \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> 
                       'var set \<Rightarrow> 'var set \<Rightarrow> ('node LDCFG_node \<times> 'var) set"
for Use::"'node \<Rightarrow> 'var set" and E::'node and X::'node 
  and H::"'var set" and L::"'var set"

where 
  lift_Use_node: 
  "V \<in> Use n \<Longrightarrow> (Node n,V) \<in> lift_Use_set Use E X H L"

  | lift_Use_High:
  "V \<in> H \<Longrightarrow> (Node E,V) \<in> lift_Use_set Use E X H L"

  | lift_Use_Low:
  "V \<in> L \<Longrightarrow> (Node X,V) \<in> lift_Use_set Use E X H L"


abbreviation lift_Use :: "('node \<Rightarrow> 'var set) \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> 
                       'var set \<Rightarrow> 'var set \<Rightarrow> 'node LDCFG_node \<Rightarrow> 'var set"
  where "lift_Use Use E X H L n \<equiv> {V. (n,V) \<in> lift_Use_set Use E X H L}"


fun lift_ParamUses :: "('node \<Rightarrow> 'var set list) \<Rightarrow> 'node LDCFG_node \<Rightarrow> 'var set list"
  where "lift_ParamUses ParamUses (Node n) =  ParamUses n"
  | "lift_ParamUses ParamUses NewEntry = []"
  | "lift_ParamUses ParamUses NewExit = []"


fun lift_ParamDefs :: "('node \<Rightarrow> 'var list) \<Rightarrow> 'node LDCFG_node \<Rightarrow> 'var list"
  where "lift_ParamDefs ParamDefs (Node n) =  ParamDefs n"
  | "lift_ParamDefs ParamDefs NewEntry = []"
  | "lift_ParamDefs ParamDefs NewExit = []"



subsection {* The lifting lemmas *}


subsubsection {* Lifting the CFG locales *}

abbreviation src :: "('edge,'node,'var,'val,'ret,'pname) LDCFG_edge \<Rightarrow> 'node LDCFG_node"
  where "src a \<equiv> fst a"

abbreviation trg :: "('edge,'node,'var,'val,'ret,'pname) LDCFG_edge \<Rightarrow> 'node LDCFG_node"
  where "trg a \<equiv> snd(snd a)"

abbreviation knd :: "('edge,'node,'var,'val,'ret,'pname) LDCFG_edge \<Rightarrow> 
  ('var,'val,'ret,'pname) edge_kind"
  where "knd a \<equiv> fst(snd a)"


lemma lift_CFG:
  assumes wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit"
  shows "CFG src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main"
proof -
  interpret CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule wf)
  interpret Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit
    by(rule pd)
  show ?thesis
  proof
    fix a assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "trg a = NewEntry"
    thus False by(fastforce elim:lift_valid_edge.cases)
  next
    show "lift_get_proc get_proc Main NewEntry = Main" by simp
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "src a = NewEntry"
    thus False by(fastforce elim:lift_valid_edge.cases)
  next
    fix a a' 
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
      and "src a = src a'" and "trg a = trg a'"
    thus "a = a'"
    proof(induct rule:lift_valid_edge.induct)
      case lve_edge thus ?case by -(erule lift_valid_edge.cases,auto dest:edge_det)
    qed(auto elim:lift_valid_edge.cases)
  next
    fix a Q r f
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>f"
    thus False by(fastforce elim:lift_valid_edge.cases dest:Main_no_call_target)
  next
    fix a Q' f'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>Main\<^esub>f'"
    thus False by(fastforce elim:lift_valid_edge.cases dest:Main_no_return_source)
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "\<exists>ins outs. (p, ins, outs) \<in> set procs"
      by(fastforce elim:lift_valid_edge.cases intro:callee_in_procs)
  next
    fix a assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "intra_kind (knd a)"
    thus "lift_get_proc get_proc Main (src a) = lift_get_proc get_proc Main (trg a)"
      by(fastforce elim:lift_valid_edge.cases intro:get_proc_intra 
                  simp:get_proc_Entry get_proc_Exit)
  next
    fix a Q r p fs 
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "lift_get_proc get_proc Main (trg a) = p"
      by(fastforce elim:lift_valid_edge.cases intro:get_proc_call)
  next
    fix a Q' p f'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    thus "lift_get_proc get_proc Main (src a) = p"
      by(fastforce elim:lift_valid_edge.cases intro:get_proc_return)
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    then obtain ax where "valid_edge ax" and "kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "sourcenode ax \<noteq> Entry \<or> targetnode ax \<noteq> Exit"
      and "src a = Node (sourcenode ax)" and "trg a = Node (targetnode ax)"
      by(fastforce elim:lift_valid_edge.cases)
    from `valid_edge ax` `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have all:"\<forall>a'. valid_edge a' \<and> targetnode a' = targetnode ax \<longrightarrow> 
               (\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
      by(auto dest:call_edges_only)
    { fix a' 
      assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
        and "trg a' = trg a"
      hence "\<exists>Qx rx fsx. knd a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx"
      proof(induct rule:lift_valid_edge.induct)
        case (lve_edge ax' e)
        note [simp] = `e = (Node (sourcenode ax'), kind ax', Node (targetnode ax'))`
        from `trg e = trg a` `trg a = Node (targetnode ax)`
        have "targetnode ax' = targetnode ax" by simp
        with `valid_edge ax'` all have "\<exists>Qx rx fsx. kind ax' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx" by blast
        thus ?case by simp
      next
        case (lve_Entry_edge e)
        from `e = (NewEntry, (\<lambda>s. True)\<^sub>\<surd>, Node Entry)` `trg e = trg a`
          `trg a = Node (targetnode ax)`
        have "targetnode ax = Entry" by simp
        with `valid_edge ax` have False by(rule Entry_target)
        thus ?case by simp
      next
        case (lve_Exit_edge e)
        from `e = (Node Exit, (\<lambda>s. True)\<^sub>\<surd>, NewExit)` `trg e = trg a`
          `trg a = Node (targetnode ax)` have False by simp
        thus ?case by simp
      next
        case (lve_Entry_Exit_edge e)
        from `e = (NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)` `trg e = trg a`
          `trg a = Node (targetnode ax)` have False by simp
        thus ?case by simp
      qed }
    thus "\<forall>a'. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a' \<and>
               trg a' = trg a \<longrightarrow> (\<exists>Qx rx fsx. knd a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)" by simp
  next
    fix a Q' p f'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    then obtain ax where "valid_edge ax" and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
      and "sourcenode ax \<noteq> Entry \<or> targetnode ax \<noteq> Exit"
      and "src a = Node (sourcenode ax)" and "trg a = Node (targetnode ax)"
      by(fastforce elim:lift_valid_edge.cases)
    from `valid_edge ax` `kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
    have all:"\<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode ax \<longrightarrow> 
            (\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)"
      by(auto dest:return_edges_only)
    { fix a' 
      assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
        and "src a' = src a"
      hence "\<exists>Qx fx. knd a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx"
      proof(induct rule:lift_valid_edge.induct)
        case (lve_edge ax' e)
        note [simp] = `e = (Node (sourcenode ax'), kind ax', Node (targetnode ax'))`
        from `src e = src a` `src a = Node (sourcenode ax)`
        have "sourcenode ax' = sourcenode ax" by simp
        with `valid_edge ax'` all have "\<exists>Qx fx. kind ax' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx" by blast
        thus ?case by simp
      next
        case (lve_Entry_edge e)
        from `e = (NewEntry, (\<lambda>s. True)\<^sub>\<surd>, Node Entry)` `src e = src a`
          `src a = Node (sourcenode ax)` have False by simp
        thus ?case by simp
      next
        case (lve_Exit_edge e)
        from `e = (Node Exit, (\<lambda>s. True)\<^sub>\<surd>, NewExit)` `src e = src a`
          `src a = Node (sourcenode ax)` have "sourcenode ax = Exit" by simp
        with `valid_edge ax` have False by(rule Exit_source)
        thus ?case by simp
      next
        case (lve_Entry_Exit_edge e)
        from `e = (NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)` `src e = src a`
          `src a = Node (sourcenode ax)` have False by simp
        thus ?case by simp
      qed }
    thus "\<forall>a'. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a' \<and>
               src a' = src a \<longrightarrow> (\<exists>Qx fx. knd a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)" by simp
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "lift_get_return_edges get_return_edges valid_edge 
      sourcenode targetnode kind a \<noteq> {}"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge ax e)
      from `e = (Node (sourcenode ax), kind ax, Node (targetnode ax))` 
        `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      with `valid_edge ax` have "get_return_edges ax \<noteq> {}"
        by(rule get_return_edge_call)
      then obtain ax' where "ax' \<in> get_return_edges ax" by blast
      with `e = (Node (sourcenode ax), kind ax, Node (targetnode ax))` `valid_edge ax`
      have "(Node (sourcenode ax'),kind ax',Node (targetnode ax')) \<in> 
        lift_get_return_edges get_return_edges valid_edge 
        sourcenode targetnode kind e"
        by(fastforce intro:lift_get_return_edgesI)
      thus ?case by fastforce
    qed simp_all
  next
    fix a a'
    assume "a' \<in> lift_get_return_edges get_return_edges valid_edge 
      sourcenode targetnode kind a"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
    proof (induct rule:lift_get_return_edges.induct)
      case (lift_get_return_edgesI ax a' e')
      from `valid_edge ax` `a' \<in> get_return_edges ax` have "valid_edge a'" 
        by(rule get_return_edges_valid)
      from `valid_edge ax` `a' \<in> get_return_edges ax` obtain Q r p fs 
        where "kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by(fastforce dest!:only_call_get_return_edges)
      with `valid_edge ax` `a' \<in> get_return_edges ax` obtain Q' f' 
        where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "get_proc(sourcenode a') = p"
        by(rule get_proc_return)
      have "sourcenode a' \<noteq> Entry"
      proof
        assume "sourcenode a' = Entry"
        with get_proc_Entry `get_proc(sourcenode a') = p` have "p = Main" by simp
        with `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "kind a' = Q'\<hookleftarrow>\<^bsub>Main\<^esub>f'" by simp
        with `valid_edge a'` show False by(rule Main_no_return_source)
      qed
      with `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))` 
        `valid_edge a'`
      show ?case by(fastforce intro:lve_edge)
    qed
  next
    fix a a'
    assume "a' \<in> lift_get_return_edges get_return_edges valid_edge sourcenode
      targetnode kind a"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "\<exists>Q r p fs. knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    proof (induct rule:lift_get_return_edges.induct)
      case (lift_get_return_edgesI ax a' e') 
      from `valid_edge ax` `a' \<in> get_return_edges ax` 
      have "\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
        by(rule only_call_get_return_edges)
      with `a = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
      show ?case by simp
    qed
  next
    fix a Q r p fs a'
    assume "a' \<in> lift_get_return_edges get_return_edges 
      valid_edge sourcenode targetnode kind a" and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "\<exists>Q' f'. knd a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    proof (induct rule:lift_get_return_edges.induct)
      case (lift_get_return_edgesI ax a' e')
      from `a = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
        `knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      with `valid_edge ax` `a' \<in> get_return_edges ax` have "\<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
        by -(rule call_return_edges)
      with `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))`
      show ?case by simp
    qed
  next
    fix a Q' p f'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    thus "\<exists>!a'. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a' \<and>
      (\<exists>Q r fs. knd a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> lift_get_return_edges get_return_edges 
      valid_edge sourcenode targetnode kind a'"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        `knd e = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by simp
      with `valid_edge a`
      have "\<exists>!a'. valid_edge a' \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> 
        a \<in> get_return_edges a'"
        by(rule return_needs_call)
      then obtain a' Q r fs where "valid_edge a'" and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
        and "a \<in> get_return_edges a'"
        and imp:"\<forall>x. valid_edge x \<and> (\<exists>Q r fs. kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> 
        a \<in> get_return_edges x \<longrightarrow> x = a'"
        by(fastforce elim:ex1E)
      let ?e' = "(Node (sourcenode a'),kind a',Node (targetnode a'))"
      have "sourcenode a' \<noteq> Entry"
      proof
        assume "sourcenode a' = Entry"
        with `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        show False by(rule Entry_no_call_source)
      qed
      with `valid_edge a'`
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e'"
        by(fastforce intro:lift_valid_edge.lve_edge)
      moreover
      from `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "knd ?e' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      moreover
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` 
        `valid_edge a'` `a \<in> get_return_edges a'`
      have "e \<in> lift_get_return_edges get_return_edges valid_edge
        sourcenode targetnode kind ?e'" by(fastforce intro:lift_get_return_edgesI)
      moreover
      { fix x
        assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x"
          and "\<exists>Q r fs. knd x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          and "e \<in> lift_get_return_edges get_return_edges valid_edge
          sourcenode targetnode kind x"
        from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x`
          `\<exists>Q r fs. knd x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain y where "valid_edge y" 
          and "x = (Node (sourcenode y), kind y, Node (targetnode y))"
          by(fastforce elim:lift_valid_edge.cases)
        with `e \<in> lift_get_return_edges get_return_edges valid_edge
          sourcenode targetnode kind x` `valid_edge a`
          `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        have "x = ?e'"
        proof(induct rule:lift_get_return_edges.induct)
          case (lift_get_return_edgesI ax ax' e)
          from `valid_edge ax` `ax' \<in> get_return_edges ax` have "valid_edge ax'"
            by(rule get_return_edges_valid)
          from `e = (Node (sourcenode ax'), kind ax', Node (targetnode ax'))`
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "sourcenode a = sourcenode ax'" and "targetnode a = targetnode ax'"
            by simp_all
          with `valid_edge a` `valid_edge ax'` have [simp]:"a = ax'" by(rule edge_det)
          from `x = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
            `\<exists>Q r fs. knd x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
          with `valid_edge ax` `ax' \<in> get_return_edges ax` imp
          have "ax = a'" by fastforce
          with `x = (Node (sourcenode ax), kind ax, Node (targetnode ax))` 
          show ?thesis by simp
        qed }
      ultimately show ?case by(blast intro:ex1I)
    qed simp_all
  next
    fix a a'
    assume "a' \<in> lift_get_return_edges get_return_edges valid_edge sourcenode
      targetnode kind a" 
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "\<exists>a''. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'' \<and>
      src a'' = trg a \<and> trg a'' = src a' \<and> knd a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    proof(induct rule:lift_get_return_edges.induct)
      case (lift_get_return_edgesI ax a' e')
      from `valid_edge ax` `a' \<in> get_return_edges ax`
      obtain ax' where "valid_edge ax'" and "sourcenode ax' = targetnode ax"
        and "targetnode ax' = sourcenode a'" and "kind ax' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(fastforce dest:intra_proc_additional_edge)
      let ?ex = "(Node (sourcenode ax'), kind ax', Node (targetnode ax'))"
      have "targetnode ax \<noteq> Entry"
      proof
        assume "targetnode ax = Entry"
        with `valid_edge ax` show False by(rule Entry_target)
      qed
      with `sourcenode ax' = targetnode ax` have "sourcenode ax' \<noteq> Entry" by simp
      with `valid_edge ax'` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?ex"
        by(fastforce intro:lve_edge)
      with `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))`
        `a = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
        `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))`
        `sourcenode ax' = targetnode ax` `targetnode ax' = sourcenode a'`
        `kind ax' = (\<lambda>cf. False)\<^sub>\<surd>`
      show ?case by simp
    qed
  next
    fix a a'
    assume "a' \<in> lift_get_return_edges get_return_edges valid_edge sourcenode
      targetnode kind a" 
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "\<exists>a''. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'' \<and>
      src a'' = src a \<and> trg a'' = trg a' \<and> knd a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    proof(induct rule:lift_get_return_edges.induct)
      case (lift_get_return_edgesI ax a' e')
      from `valid_edge ax` `a' \<in> get_return_edges ax`
      obtain ax' where "valid_edge ax'" and "sourcenode ax' = sourcenode ax"
        and "targetnode ax' = targetnode a'" and "kind ax' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(fastforce dest:call_return_node_edge)
      let ?ex = "(Node (sourcenode ax'), kind ax', Node (targetnode ax'))"
      from `valid_edge ax` `a' \<in> get_return_edges ax`
      obtain Q r p fs where "kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
        by(fastforce dest!:only_call_get_return_edges)
      have "sourcenode ax \<noteq> Entry"
      proof
        assume "sourcenode ax = Entry"
        with `valid_edge ax` `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show False
          by(rule Entry_no_call_source)
      qed
      with `sourcenode ax' = sourcenode ax` have "sourcenode ax' \<noteq> Entry" by simp
      with `valid_edge ax'` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?ex"
        by(fastforce intro:lve_edge)
      with `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))`
        `a = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
        `e' = (Node (sourcenode a'), kind a', Node (targetnode a'))`
        `sourcenode ax' = sourcenode ax` `targetnode ax' = targetnode a'`
        `kind ax' = (\<lambda>cf. False)\<^sub>\<surd>`
      show ?case by simp
    qed
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "\<exists>!a'. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a' \<and>
      src a' = src a \<and> intra_kind (knd a')"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      with `valid_edge a` have "\<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and>
        intra_kind(kind a')" by(rule call_only_one_intra_edge)
      then obtain a' where "valid_edge a'" and "sourcenode a' = sourcenode a"
        and "intra_kind(kind a')" 
        and imp:"\<forall>x. valid_edge x \<and> sourcenode x = sourcenode a \<and> intra_kind(kind x)
        \<longrightarrow> x = a'" by(fastforce elim:ex1E)
      let ?e' = "(Node (sourcenode a'), kind a', Node (targetnode a'))"
      have "sourcenode a \<noteq> Entry"
      proof
        assume "sourcenode a = Entry"
        with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show False
          by(rule Entry_no_call_source)
      qed
      with `sourcenode a' = sourcenode a` have "sourcenode a' \<noteq> Entry" by simp
      with `valid_edge a'` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e'"
        by(fastforce intro:lift_valid_edge.lve_edge)
      moreover
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        `sourcenode a' = sourcenode a`
      have "src ?e' = src e" by simp
      moreover
      from `intra_kind(kind a')` have "intra_kind (knd ?e')" by simp
      moreover
      { fix x 
        assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x"
          and "src x = src e" and "intra_kind (knd x)"
        from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x`
        have "x = ?e'"
        proof(induct rule:lift_valid_edge.cases)
          case (lve_edge ax ex)
          from `intra_kind (knd x)` `x = ex` `src x = src e`
            `ex = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "intra_kind (kind ax)" and "sourcenode ax = sourcenode a" by simp_all
          with `valid_edge ax` imp have "ax = a'" by fastforce
          with `x = ex` `ex = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
          show ?case by simp
        next
          case (lve_Entry_edge ex)
          with `src x = src e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have False by simp
          thus ?case by simp
        next
          case (lve_Exit_edge ex)
          with `src x = src e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "sourcenode a = Exit" by simp
          with `valid_edge a` have False by(rule Exit_source)
          thus ?case by simp
        next
          case (lve_Entry_Exit_edge ex)
          with `src x = src e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have False by simp
          thus ?case by simp
        qed }
      ultimately show ?case by(blast intro:ex1I)
    qed simp_all
  next
    fix a Q' p f'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    thus "\<exists>!a'. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a' \<and>
      trg a' = trg a \<and> intra_kind (knd a')"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by simp
      with `valid_edge a` have "\<exists>!a'. valid_edge a' \<and> targetnode a' = targetnode a \<and>
        intra_kind(kind a')" by(rule return_only_one_intra_edge)
      then obtain a' where "valid_edge a'" and "targetnode a' = targetnode a"
        and "intra_kind(kind a')" 
        and imp:"\<forall>x. valid_edge x \<and> targetnode x = targetnode a \<and> intra_kind(kind x)
        \<longrightarrow> x = a'" by(fastforce elim:ex1E)
      let ?e' = "(Node (sourcenode a'), kind a', Node (targetnode a'))"
      have "targetnode a \<noteq> Exit"
      proof
        assume "targetnode a = Exit"
        with `valid_edge a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` show False
          by(rule Exit_no_return_target)
      qed
      with `targetnode a' = targetnode a` have "targetnode a' \<noteq> Exit" by simp
      with `valid_edge a'` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e'"
        by(fastforce intro:lift_valid_edge.lve_edge)
      moreover
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        `targetnode a' = targetnode a`
      have "trg ?e' = trg e" by simp
      moreover
      from `intra_kind(kind a')` have "intra_kind (knd ?e')" by simp
      moreover
      { fix x 
        assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x"
          and "trg x = trg e" and "intra_kind (knd x)"
        from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit x`
        have "x = ?e'"
        proof(induct rule:lift_valid_edge.cases)
          case (lve_edge ax ex)
          from `intra_kind (knd x)` `x = ex` `trg x = trg e`
            `ex = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "intra_kind (kind ax)" and "targetnode ax = targetnode a" by simp_all
          with `valid_edge ax` imp have "ax = a'" by fastforce
          with `x = ex` `ex = (Node (sourcenode ax), kind ax, Node (targetnode ax))`
          show ?case by simp
        next
          case (lve_Entry_edge ex)
          with `trg x = trg e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "targetnode a = Entry" by simp
          with `valid_edge a` have False by(rule Entry_target)
          thus ?case by simp
        next
          case (lve_Exit_edge ex)
          with `trg x = trg e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have False by simp
          thus ?case by simp
        next
          case (lve_Entry_Exit_edge ex)
          with `trg x = trg e` 
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have False by simp
          thus ?case by simp
        qed }
      ultimately show ?case by(blast intro:ex1I)
    qed simp_all
  next
    fix a a' Q\<^sub>1 r\<^sub>1 p fs\<^sub>1 Q\<^sub>2 r\<^sub>2 fs\<^sub>2
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
      and "knd a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1" and "knd a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2"
    then obtain x x' where "valid_edge x" 
      and a:"a = (Node (sourcenode x),kind x,Node (targetnode x))" and "valid_edge x'"
      and a':"a' = (Node (sourcenode x'),kind x',Node (targetnode x'))"
      by(auto elim!:lift_valid_edge.cases)
    with `knd a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1` `knd a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2`
    have "kind x = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1" and "kind x' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2" by simp_all
    with `valid_edge x` `valid_edge x'` have "targetnode x = targetnode x'"
      by(rule same_proc_call_unique_target)
    with a a' show "trg a = trg a'" by simp
  next
    from unique_callers show "distinct_fst procs" .
  next
    fix p ins outs
    assume "(p, ins, outs) \<in> set procs"
    from distinct_formal_ins[OF this] show "distinct ins" .
  next
    fix p ins outs
    assume "(p, ins, outs) \<in> set procs"
    from distinct_formal_outs[OF this] show "distinct outs" .
  qed
qed


lemma lift_CFG_wf:
  assumes wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit"
  shows "CFG_wf src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main (lift_Def Def Entry Exit H L) (lift_Use Use Entry Exit H L)
  (lift_ParamDefs ParamDefs) (lift_ParamUses ParamUses)"
proof -
  interpret CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule wf)
  interpret Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit
    by(rule pd)
  interpret CFG:CFG src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main" 
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main
    by(fastforce intro:lift_CFG wf pd)
  show ?thesis
  proof
    show "lift_Def Def Entry Exit H L NewEntry = {} \<and>
          lift_Use Use Entry Exit H L NewEntry = {}"
      by(fastforce elim:lift_Use_set.cases lift_Def_set.cases)
  next
    fix a Q r p fs ins outs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "(p, ins, outs) \<in> set procs"
    thus "length (lift_ParamUses ParamUses (src a)) = length ins"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "src e = Node (sourcenode a)" by simp_all
      with `valid_edge a` `(p,ins,outs) \<in> set procs`
      have "length(ParamUses (sourcenode a)) = length ins"
        by -(rule ParamUses_call_source_length)
      with `src e = Node (sourcenode a)` show ?case by simp
    qed simp_all
  next
    fix a assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
    thus "distinct (lift_ParamDefs ParamDefs (trg a))"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `valid_edge a` have "distinct (ParamDefs (targetnode a))"
        by(rule distinct_ParamDefs)
      with `e = (Node (sourcenode a), kind a, Node (targetnode a))`
      show ?case by simp
    next
      case (lve_Entry_edge e)
      have "ParamDefs Entry = []"
      proof(rule ccontr)
        assume "ParamDefs Entry \<noteq> []"
        then obtain V Vs where "ParamDefs Entry = V#Vs" 
          by(cases "ParamDefs Entry") auto
        hence "V \<in> set (ParamDefs Entry)" by fastforce
        hence "V \<in> Def Entry" by(fastforce intro:ParamDefs_in_Def)
        with Entry_empty show False by simp
      qed
      with `e = (NewEntry, (\<lambda>s. True)\<^sub>\<surd>, Node Entry)` show ?case by simp
    qed simp_all
  next
    fix a Q' p f' ins outs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "(p, ins, outs) \<in> set procs"
    thus "length (lift_ParamDefs ParamDefs (trg a)) = length outs"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        `knd e = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "trg e = Node (targetnode a)" by simp_all
      with `valid_edge a` `(p,ins,outs) \<in> set procs`
      have "length(ParamDefs (targetnode a)) = length outs"
        by -(rule ParamDefs_return_target_length)
      with `trg e = Node (targetnode a)` show ?case by simp
    qed simp_all
  next
    fix n V
    assume "CFG.CFG.valid_node src trg 
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) n"
      and "V \<in> set (lift_ParamDefs ParamDefs n)"
    hence "((n = NewEntry) \<or> n = NewExit) \<or> (\<exists>m. n = Node m \<and> valid_node m)"
      by(auto elim:lift_valid_edge.cases simp:CFG.valid_node_def)
    thus "V \<in> lift_Def Def Entry Exit H L n" apply -
    proof(erule disjE)+
      assume "n = NewEntry"
      with `V \<in> set (lift_ParamDefs ParamDefs n)` show ?thesis by simp
    next
       assume "n = NewExit"
      with `V \<in> set (lift_ParamDefs ParamDefs n)` show ?thesis by simp
    next
      assume "\<exists>m. n = Node m \<and> valid_node m"
      then obtain m where "n = Node m" and "valid_node m" by blast
      from `n = Node m` `V \<in> set (lift_ParamDefs ParamDefs n)`
      have "V \<in> set (ParamDefs m)" by simp
      with `valid_node m` have "V \<in> Def m" by(rule ParamDefs_in_Def)
      with `n = Node m` show ?thesis by(fastforce intro:lift_Def_node)
    qed
  next
    fix a Q r p fs ins outs V
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "(p, ins, outs) \<in> set procs" and "V \<in> set ins"
    thus "V \<in> lift_Def Def Entry Exit H L (trg a)"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p, ins, outs) \<in> set procs` `V \<in> set ins`
      have "V \<in> Def (targetnode a)" by(rule ins_in_Def)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
      have "trg e = Node (targetnode a)" by simp
      with `V \<in> Def (targetnode a)` show ?case by(fastforce intro:lift_Def_node)
    qed simp_all
  next
    fix a Q r p fs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "lift_Def Def Entry Exit H L (src a) = {}"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      show ?case
      proof(rule ccontr)
        assume "lift_Def Def Entry Exit H L (src e) \<noteq> {}"
        then obtain x where "x \<in> lift_Def Def Entry Exit H L (src e)" by blast
        from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
        with `valid_edge a` have "Def (sourcenode a) = {}" 
          by(rule call_source_Def_empty)
        have "sourcenode a \<noteq> Entry"
        proof
          assume "sourcenode a = Entry"
          with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          show False by(rule Entry_no_call_source)
        qed
        from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        have "src e = Node (sourcenode a)" by simp
        with `Def (sourcenode a) = {}` `x \<in> lift_Def Def Entry Exit H L (src e)`
          `sourcenode a \<noteq> Entry`
        show False by(fastforce elim:lift_Def_set.cases)
      qed 
    qed simp_all
  next
    fix n V
    assume "CFG.CFG.valid_node src trg 
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) n"
      and "V \<in> \<Union>set (lift_ParamUses ParamUses n)"
    hence "((n = NewEntry) \<or> n = NewExit) \<or> (\<exists>m. n = Node m \<and> valid_node m)"
      by(auto elim:lift_valid_edge.cases simp:CFG.valid_node_def)
    thus "V \<in> lift_Use Use Entry Exit H L n" apply -
    proof(erule disjE)+
      assume "n = NewEntry"
      with `V \<in> \<Union>set (lift_ParamUses ParamUses n)` show ?thesis by simp
    next
      assume "n = NewExit"
      with `V \<in> \<Union>set (lift_ParamUses ParamUses n)` show ?thesis by simp
    next
      assume "\<exists>m. n = Node m \<and> valid_node m"
      then obtain m where "n = Node m" and "valid_node m" by blast
      from `V \<in> \<Union>set (lift_ParamUses ParamUses n)` `n = Node m`
      have "V \<in> \<Union>set (ParamUses m)" by simp
      with `valid_node m` have "V \<in> Use m" by(rule ParamUses_in_Use)
      with `n = Node m` show ?thesis by(fastforce intro:lift_Use_node)
    qed
  next
    fix a Q p f ins outs V
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "(p, ins, outs) \<in> set procs" and "V \<in> set outs"
    thus "V \<in> lift_Use Use Entry Exit H L (src a)"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by simp
      from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p, ins, outs) \<in> set procs` `V \<in> set outs`
      have "V \<in> Use (sourcenode a)" by(rule outs_in_Use)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
      have "src e = Node (sourcenode a)" by simp
      with `V \<in> Use (sourcenode a)` show ?case by(fastforce intro:lift_Use_node)
    qed simp_all
  next
    fix a V s
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "V \<notin> lift_Def Def Entry Exit H L (src a)" and "intra_kind (knd a)"
      and "pred (knd a) s"
    thus "state_val (transfer (knd a) s) V = state_val s V"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` 
        `intra_kind (knd e)` `pred (knd e) s`
      have "intra_kind (kind a)" and "pred (kind a) s" 
        and "knd e = kind a" and "src e = Node (sourcenode a)" by simp_all
      from `V \<notin> lift_Def Def Entry Exit H L (src e)` `src e = Node (sourcenode a)`
      have "V \<notin> Def (sourcenode a)" by (auto dest: lift_Def_node)
      from `valid_edge a` `V \<notin> Def (sourcenode a)` `intra_kind (kind a)` 
        `pred (kind a) s`
      have "state_val (transfer (kind a) s) V = state_val s V" 
        by(rule CFG_intra_edge_no_Def_equal)
      with `knd e = kind a` show ?case by simp
    next
      case (lve_Entry_edge e)
      from `e = (NewEntry, (\<lambda>s. True)\<^sub>\<surd>, Node Entry)` `pred (knd e) s`
      show ?case by(cases s) auto
    next
      case (lve_Exit_edge e)
      from `e = (Node Exit, (\<lambda>s. True)\<^sub>\<surd>, NewExit)` `pred (knd e) s`
      show ?case by(cases s) auto
    next
      case (lve_Entry_Exit_edge e)
      from `e = (NewEntry, (\<lambda>s. False)\<^sub>\<surd>, NewExit)` `pred (knd e) s`
      have False by(cases s) auto
      thus ?case by simp
    qed
  next
    fix a s s'
    assume assms:"lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      "\<forall>V\<in>lift_Use Use Entry Exit H L (src a). state_val s V = state_val s' V"
      "intra_kind (knd a)" "pred (knd a) s" "pred (knd a) s'"
    show "\<forall>V\<in>lift_Def Def Entry Exit H L (src a).
      state_val (transfer (knd a) s) V = state_val (transfer (knd a) s') V"
    proof
      fix V assume "V \<in> lift_Def Def Entry Exit H L (src a)"
      with assms
      show "state_val (transfer (knd a) s) V = state_val (transfer (knd a) s') V"
      proof(induct rule:lift_valid_edge.induct)
        case (lve_edge a e)
        from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          `intra_kind (knd e)` have "intra_kind (kind a)" by simp
        show ?case
        proof (cases "Node (sourcenode a) = Node Entry")
          case True
          hence "sourcenode a = Entry" by simp
          from Entry_Exit_edge obtain a' where "valid_edge a'"
            and "sourcenode a' = Entry" and "targetnode a' = Exit"
            and "kind a' = (\<lambda>s. False)\<^sub>\<surd>" by blast
          have "\<exists>Q. kind a = (Q)\<^sub>\<surd>"
          proof(cases "targetnode a = Exit")
            case True
            with `valid_edge a` `valid_edge a'` `sourcenode a = Entry`
              `sourcenode a' = Entry` `targetnode a' = Exit`
            have "a = a'" by(fastforce dest:edge_det)
            with `kind a' = (\<lambda>s. False)\<^sub>\<surd>` show ?thesis by simp
          next
            case False
            with `valid_edge a` `valid_edge a'` `sourcenode a = Entry`
              `sourcenode a' = Entry` `targetnode a' = Exit`
              `intra_kind (kind a)` `kind a' = (\<lambda>s. False)\<^sub>\<surd>`
            show ?thesis by(auto dest:deterministic simp:intra_kind_def)
          qed
          from True `V \<in> lift_Def Def Entry Exit H L (src e)` Entry_empty
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "V \<in> H" by(fastforce elim:lift_Def_set.cases)
          from True `e = (Node (sourcenode a), kind a, Node (targetnode a))`
            `sourcenode a \<noteq> Entry \<or> targetnode a \<noteq> Exit`
          have "\<forall>V\<in>H. V \<in> lift_Use Use Entry Exit H L (src e)"
            by(fastforce intro:lift_Use_High)
          with `\<forall>V\<in>lift_Use Use Entry Exit H L (src e). 
            state_val s V = state_val s' V` `V \<in> H`
          have "state_val s V = state_val s' V" by simp
          with `e = (Node (sourcenode a), kind a, Node (targetnode a))` 
            `\<exists>Q. kind a = (Q)\<^sub>\<surd>` `pred (knd e) s` `pred (knd e) s'`
          show ?thesis by(cases s,auto,cases s',auto)
        next
          case False
          { fix V' assume "V' \<in> Use (sourcenode a)"
            with `e = (Node (sourcenode a), kind a, Node (targetnode a))`
            have "V' \<in> lift_Use Use Entry Exit H L (src e)"
              by(fastforce intro:lift_Use_node)
          }
          with `\<forall>V\<in>lift_Use Use Entry Exit H L (src e). 
            state_val s V = state_val s' V`
          have "\<forall>V\<in>Use (sourcenode a). state_val s V = state_val s' V"
            by fastforce
          from `valid_edge a` this `pred (knd e) s` `pred (knd e) s'`
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
            `intra_kind (knd e)`
          have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s) V =
            state_val (transfer (kind a) s') V"
            by -(erule CFG_intra_edge_transfer_uses_only_Use,auto)
          from `V \<in> lift_Def Def Entry Exit H L (src e)` False
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          have "V \<in> Def (sourcenode a)" by(fastforce elim:lift_Def_set.cases)
          with `\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s) V =
            state_val (transfer (kind a) s') V`
            `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          show ?thesis by simp
        qed
      next
        case (lve_Entry_edge e)
        from `V \<in> lift_Def Def Entry Exit H L (src e)` 
          `e = (NewEntry, (\<lambda>s. True)\<^sub>\<surd>, Node Entry)`
        have False by(fastforce elim:lift_Def_set.cases)
        thus ?case by simp
      next
        case (lve_Exit_edge e)
        from `V \<in> lift_Def Def Entry Exit H L (src e)` 
          `e = (Node Exit, (\<lambda>s. True)\<^sub>\<surd>, NewExit)`
        have False
          by(fastforce elim:lift_Def_set.cases intro!:Entry_noteq_Exit simp:Exit_empty)
        thus ?case  by simp
      next
        case (lve_Entry_Exit_edge e)
        thus ?case by(cases s) auto
      qed
    qed
  next
    fix a s s'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "pred (knd a) s" and "snd (hd s) = snd (hd s')"
      and "\<forall>V\<in>lift_Use Use Entry Exit H L (src a). state_val s V = state_val s' V"
      and "length s = length s'"
    thus "pred (knd a) s'"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `pred (knd e) s`
      have "pred (kind a) s" and "src e = Node (sourcenode a)" by simp_all
      from `src e = Node (sourcenode a)` 
        `\<forall>V\<in>lift_Use Use Entry Exit H L (src e). state_val s V = state_val s' V`
      have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V"
        by(auto dest:lift_Use_node)
      from `valid_edge a` `pred (kind a) s` `snd (hd s) = snd (hd s')`
        this `length s = length s'`
      have "pred (kind a) s'" by(rule CFG_edge_Uses_pred_equal)
      with `e = (Node (sourcenode a), kind a, Node (targetnode a))`
      show ?case by simp
    next
      case (lve_Entry_edge e)
      thus ?case by(cases s') auto
    next
      case (lve_Exit_edge e)
      thus ?case by(cases s') auto
    next
      case (lve_Entry_Exit_edge e)
      thus ?case by(cases s) auto
    qed
  next
    fix a Q r p fs ins outs
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "(p, ins, outs) \<in> set procs"
    thus "length fs = length ins"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by simp
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p, ins, outs) \<in> set procs`
      show ?case by(rule CFG_call_edge_length)
    qed simp_all
  next
    fix a Q r p fs a' Q' r' p' fs' s s'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "knd a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
      and "src a = src a'" and "pred (knd a) s" and "pred (knd a') s"
    from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a`
      `knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `pred (knd a) s`
    obtain x where a:"a = (Node (sourcenode x),kind x,Node (targetnode x))" 
      and "valid_edge x" and "src a = Node (sourcenode x)" 
      and "kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "pred (kind x) s"
      by(fastforce elim:lift_valid_edge.cases)
    from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'`
      `knd a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `pred (knd a') s`
    obtain x' where a':"a' = (Node (sourcenode x'),kind x',Node (targetnode x'))" 
      and "valid_edge x'" and "src a' = Node (sourcenode x')" 
      and "kind x' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'" and "pred (kind x') s"
      by(fastforce elim:lift_valid_edge.cases)
    from `src a = Node (sourcenode x)` `src a' = Node (sourcenode x')` 
      `src a = src a'`
    have "sourcenode x = sourcenode x'" by simp
    from `valid_edge x` `kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge x'` `kind x' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
      `sourcenode x = sourcenode x'` `pred (kind x) s` `pred (kind x') s`
    have "x = x'" by(rule CFG_call_determ)
    with a a' show "a = a'" by simp
  next
    fix a Q r p fs i ins outs s s'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "i < length ins" and "(p, ins, outs) \<in> set procs"
      and "pred (knd a) s" and "pred (knd a) s'"
      and "\<forall>V\<in>lift_ParamUses ParamUses (src a) ! i. state_val s V = state_val s' V"
    thus "params fs (state_val s) ! i = CFG.params fs (state_val s') ! i"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        `pred (knd e) s` `pred (knd e) s'`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "pred (kind a) s" and "pred (kind a) s'"
        and "src e = Node (sourcenode a)"
        by simp_all
      from `\<forall>V\<in>lift_ParamUses ParamUses (src e) ! i. state_val s V = state_val s' V`
        `src e = Node (sourcenode a)`
      have "\<forall>V \<in> (ParamUses (sourcenode a))!i. state_val s V = state_val s' V" by simp
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `i < length ins` 
        `(p, ins, outs) \<in> set procs` `pred (kind a) s` `pred (kind a) s'`
      show ?case by(rule CFG_call_edge_params)
    qed simp_all
  next
    fix a Q' p f' ins outs cf cf'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "(p, ins, outs) \<in> set procs"
    thus "f' cf cf' = cf'(lift_ParamDefs ParamDefs (trg a) [:=] map cf outs)"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` `knd e = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
      have "kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "trg e = Node (targetnode a)" by simp_all
      from `valid_edge a` `kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p, ins, outs) \<in> set procs`
      have "f' cf cf' = cf'(ParamDefs (targetnode a) [:=] map cf outs)"
        by(rule CFG_return_edge_fun)
      with `trg e = Node (targetnode a)` show ?case by simp
    qed simp_all
  next
    fix a a'
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
      and "src a = src a'" and "trg a \<noteq> trg a'"
      and "intra_kind (knd a)" and "intra_kind (knd a')"
    thus "\<exists>Q Q'. knd a = (Q)\<^sub>\<surd> \<and> knd a' = (Q')\<^sub>\<surd> \<and> 
                 (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'`
        `valid_edge a` `e = (Node (sourcenode a), kind a, Node (targetnode a))`
        `src e = src a'` `trg e \<noteq> trg a'` `intra_kind (knd e)` `intra_kind (knd a')`
      show ?case
      proof(induct rule:lift_valid_edge.induct)
        case lve_edge thus ?case by(auto dest:deterministic)
      next
        case (lve_Exit_edge e')
        from `e = (Node (sourcenode a), kind a, Node (targetnode a))`
          `e' = (Node Exit, (\<lambda>s. True)\<^sub>\<surd>, NewExit)` `src e = src e'`
        have "sourcenode a = Exit" by simp
        with `valid_edge a` have False by(rule Exit_source)
        thus ?case by simp
      qed auto
    qed (fastforce elim:lift_valid_edge.cases)+
  qed
qed


lemma lift_CFGExit:
  assumes wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit"
  shows "CFGExit src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main NewExit"
proof -
  interpret CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule wf)
  interpret Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit
    by(rule pd)
  interpret CFG:CFG src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main" 
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main
    by(fastforce intro:lift_CFG wf pd)
  show ?thesis
  proof
    fix a assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "src a = NewExit"
    thus False by(fastforce elim:lift_valid_edge.cases)
  next
    show "lift_get_proc get_proc Main NewExit = Main" by simp
  next
    fix a Q p f
    assume "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      and "knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "trg a = NewExit"
    thus False by(fastforce elim:lift_valid_edge.cases)
  next
    show "\<exists>a. lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a \<and>
      src a = NewEntry \<and> trg a = NewExit \<and> knd a = (\<lambda>s. False)\<^sub>\<surd>"
      by(fastforce intro:lve_Entry_Exit_edge)
  qed
qed


lemma lift_CFGExit_wf:
  assumes wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit"
  shows "CFGExit_wf src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main NewExit (lift_Def Def Entry Exit H L) (lift_Use Use Entry Exit H L)
  (lift_ParamDefs ParamDefs) (lift_ParamUses ParamUses)"
proof -
  interpret CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule wf)
  interpret Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit
    by(rule pd)
  interpret CFG_wf:CFG_wf src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main" 
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main "lift_Def Def Entry Exit H L" "lift_Use Use Entry Exit H L"
    "lift_ParamDefs ParamDefs" "lift_ParamUses ParamUses"
    by(fastforce intro:lift_CFG_wf wf pd)
  interpret CFGExit:CFGExit src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main"
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main NewExit 
    by(fastforce intro:lift_CFGExit wf pd)
  show ?thesis
  proof
    show "lift_Def Def Entry Exit H L NewExit = {} \<and>
      lift_Use Use Entry Exit H L NewExit = {}" 
      by(fastforce elim:lift_Def_set.cases lift_Use_set.cases)
  qed
qed


subsubsection {* Lifting the SDG *}



lemma lift_Postdomination:
  assumes wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit"
  and inner:"CFGExit.inner_node sourcenode targetnode valid_edge Entry Exit nx"
  shows "Postdomination src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main NewExit"
proof -
  interpret CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule wf)
  interpret Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit
    by(rule pd)
  interpret CFGExit:CFGExit src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main"
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main NewExit 
    by(fastforce intro:lift_CFGExit wf pd)
  { fix m assume "valid_node m"
    then obtain a where "valid_edge a" and "m = sourcenode a \<or> m = targetnode a"
      by(auto simp:valid_node_def)
    from `m = sourcenode a \<or> m = targetnode a`
    have "CFG.CFG.valid_node src trg
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) (Node m)"
    proof
      assume "m = sourcenode a"
      show ?thesis
      proof(cases "m = Entry")
        case True
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)" by(fastforce intro:lve_Entry_edge)
        with `m = Entry` show ?thesis by(fastforce simp:CFGExit.valid_node_def)
      next
        case False
        with `m = sourcenode a` `valid_edge a`
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node (sourcenode a),kind a,Node(targetnode a))"
          by(fastforce intro:lve_edge)
        with `m = sourcenode a` show ?thesis by(fastforce simp:CFGExit.valid_node_def)
      qed
    next
      assume "m = targetnode a"
      show ?thesis
      proof(cases "m = Exit")
        case True
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Exit_edge)
        with `m = Exit` show ?thesis by(fastforce simp:CFGExit.valid_node_def)
      next
        case False
        with `m = targetnode a` `valid_edge a`
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node (sourcenode a),kind a,Node(targetnode a))"
          by(fastforce intro:lve_edge)
        with `m = targetnode a` show ?thesis by(fastforce simp:CFGExit.valid_node_def)
      qed
    qed }
  note lift_valid_node = this
  { fix n as n' cs m m'
    assume "valid_path_aux cs as" and "m -as\<rightarrow>* m'" and "\<forall>c \<in> set cs. valid_edge c"
      and "m \<noteq> Entry \<or> m' \<noteq> Exit"
    hence "\<exists>cs' es. CFG.CFG.valid_path_aux knd
      (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
      cs' es \<and> 
      list_all2 (\<lambda>c c'. c' = (Node (sourcenode c),kind c,Node (targetnode c))) cs cs' 
       \<and> CFG.CFG.path src trg
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
      (Node m) es (Node m')"
    proof(induct arbitrary:m rule:vpa_induct)
      case (vpa_empty cs)
      from `m -[]\<rightarrow>* m'` have [simp]:"m = m'" by fastforce
      from `m -[]\<rightarrow>* m'` have "valid_node m" by(rule path_valid_node)
      obtain cs' where "cs' = 
        map (\<lambda>c. (Node (sourcenode c),kind c,Node (targetnode c))) cs" by simp
      hence "list_all2 
        (\<lambda>c c'. c' = (Node (sourcenode c),kind c,Node (targetnode c))) cs cs'"
        by(simp add:list_all2_conv_all_nth)
      with `valid_node m` show ?case
        apply(rule_tac x="cs'" in exI)
        apply(rule_tac x="[]" in exI)
        by(fastforce intro:CFGExit.empty_path lift_valid_node)
    next
      case (vpa_intra cs a as)
      note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; \<forall>c\<in>set cs. valid_edge c; m \<noteq> Entry \<or> m' \<noteq> Exit\<rbrakk> \<Longrightarrow>
        \<exists>cs' es. CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) cs' es \<and>
        list_all2 (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) cs
        cs' \<and> CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) es (Node m')`
      from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
        and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
      show ?case
      proof(cases "sourcenode a = Entry \<and> targetnode a = Exit")
        case True
        with `m = sourcenode a` `m \<noteq> Entry \<or> m' \<noteq> Exit`
        have "m' \<noteq> Exit" by simp
        from True have "targetnode a = Exit" by simp
        with `targetnode a -as\<rightarrow>* m'` have "m' = Exit"
          by -(drule path_Exit_source,auto)
        with `m' \<noteq> Exit` have False by simp
        thus ?thesis by simp
      next
        case False
        let ?e = "(Node (sourcenode a),kind a,Node (targetnode a))"
        from False `valid_edge a` 
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e"
          by(fastforce intro:lve_edge)
        have "targetnode a \<noteq> Entry"
        proof
          assume "targetnode a = Entry"
          with `valid_edge a` show False by(rule Entry_target)
        qed
        hence "targetnode a \<noteq> Entry \<or> m' \<noteq> Exit" by simp
        from IH[OF `targetnode a -as\<rightarrow>* m'` `\<forall>c\<in>set cs. valid_edge c` this] 
        obtain cs' es
          where valid_path:"CFG.valid_path_aux knd
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) cs' es" 
          and list:"list_all2 
          (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) cs cs'"
          and path:"CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node (targetnode a)) es (Node m')" by blast
        from `intra_kind (kind a)` valid_path have "CFG.valid_path_aux knd
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) cs' (?e#es)" by(fastforce simp:intra_kind_def)
        moreover
        from path `m = sourcenode a` 
          `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e`
        have "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node m) (?e#es) (Node m')" by(fastforce intro:CFGExit.Cons_path)
        ultimately show ?thesis using list by blast
      qed
    next
      case (vpa_Call cs a as Q r p fs)
      note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; \<forall>c\<in>set (a # cs). valid_edge c; 
        m \<noteq> Entry \<or> m' \<noteq> Exit\<rbrakk> \<Longrightarrow>
        \<exists>cs' es. CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) cs' es \<and>
        list_all2 (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) 
        (a#cs) cs' \<and> CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) es (Node m')`
      from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
        and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
      from `\<forall>c\<in>set cs. valid_edge c` `valid_edge a` 
      have "\<forall>c\<in>set (a # cs). valid_edge c" by simp
      let ?e = "(Node (sourcenode a),kind a,Node (targetnode a))"
      have "sourcenode a \<noteq> Entry"
      proof
        assume "sourcenode a = Entry"
        with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
        show False by(rule Entry_no_call_source)
      qed
      with `valid_edge a` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e"
        by(fastforce intro:lve_edge)
      have "targetnode a \<noteq> Entry"
      proof
        assume "targetnode a = Entry"
        with `valid_edge a` show False by(rule Entry_target)
      qed
      hence "targetnode a \<noteq> Entry \<or> m' \<noteq> Exit" by simp
      from IH[OF `targetnode a -as\<rightarrow>* m'` `\<forall>c\<in>set (a # cs). valid_edge c` this]
      obtain cs' es
        where valid_path:"CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode 
        targetnode kind) cs' es" 
        and list:"list_all2 
        (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) (a#cs) cs'"
        and path:"CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node (targetnode a)) es (Node m')" by blast
      from list obtain cx csx where "cs' = cx#csx"
        and cx:"cx = (Node (sourcenode a), kind a, Node (targetnode a))"
        and list':"list_all2 
        (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) cs csx"
        by(fastforce simp:list_all2_Cons1)
      from valid_path cx `cs' = cx#csx` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode 
        targetnode kind) csx (?e#es)" by simp
      moreover
      from path `m = sourcenode a` 
        `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e`
      have "CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) (?e#es) (Node m')" by(fastforce intro:CFGExit.Cons_path)
      ultimately show ?case using list' by blast
    next
      case (vpa_ReturnEmpty cs a as Q p f)
      note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; \<forall>c\<in>set []. valid_edge c; m \<noteq> Entry \<or> m' \<noteq> Exit\<rbrakk> \<Longrightarrow>
        \<exists>cs' es. CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) cs' es \<and>
        list_all2 (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) 
        [] cs' \<and> CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) es (Node m')`
      from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
        and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
      let ?e = "(Node (sourcenode a),kind a,Node (targetnode a))"
      have "targetnode a \<noteq> Exit"
      proof
        assume "targetnode a = Exit"
        with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show False by(rule Exit_no_return_target)
      qed
      with `valid_edge a` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e"
        by(fastforce intro:lve_edge)
      have "targetnode a \<noteq> Entry"
      proof
        assume "targetnode a = Entry"
        with `valid_edge a` show False by(rule Entry_target)
      qed
      hence "targetnode a \<noteq> Entry \<or> m' \<noteq> Exit" by simp
      from IH[OF `targetnode a -as\<rightarrow>* m'` _ this] obtain es
        where valid_path:"CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) [] es"
        and path:"CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node (targetnode a)) es (Node m')" by auto
      from valid_path `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode 
        targetnode kind) [] (?e#es)" by simp
      moreover
      from path `m = sourcenode a` 
        `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e`
      have "CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) (?e#es) (Node m')" by(fastforce intro:CFGExit.Cons_path)
      ultimately show ?case using `cs = []` by blast
    next
      case (vpa_ReturnCons cs a as Q p f c' cs')
      note IH = `\<And>m. \<lbrakk>m -as\<rightarrow>* m'; \<forall>c\<in>set cs'. valid_edge c; m \<noteq> Entry \<or> m' \<noteq> Exit\<rbrakk> \<Longrightarrow>
        \<exists>csx es. CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) csx es \<and>
        list_all2 (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) 
        cs' csx \<and> CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) es (Node m')`
      from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
        and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
      from `\<forall>c\<in>set cs. valid_edge c` `cs = c' # cs'`
      have "valid_edge c'" and "\<forall>c\<in>set cs'. valid_edge c" by simp_all
      let ?e = "(Node (sourcenode a),kind a,Node (targetnode a))"
      have "targetnode a \<noteq> Exit"
      proof
        assume "targetnode a = Exit"
        with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show False by(rule Exit_no_return_target)
      qed
      with `valid_edge a` 
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e"
        by(fastforce intro:lve_edge)
      have "targetnode a \<noteq> Entry"
      proof
        assume "targetnode a = Entry"
        with `valid_edge a` show False by(rule Entry_target)
      qed
      hence "targetnode a \<noteq> Entry \<or> m' \<noteq> Exit" by simp
      from IH[OF `targetnode a -as\<rightarrow>* m'` `\<forall>c\<in>set cs'. valid_edge c` this] 
      obtain csx es
        where valid_path:"CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind) csx es"
        and list:"list_all2 
        (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) cs' csx"
        and path:"CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node (targetnode a)) es (Node m')" by blast
      from `valid_edge c'` `a \<in> get_return_edges c'`
      have "?e \<in> lift_get_return_edges get_return_edges valid_edge sourcenode
        targetnode kind (Node (sourcenode c'),kind c',Node (targetnode c'))"
        by(fastforce intro:lift_get_return_edgesI)
      with valid_path `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
      have "CFG.valid_path_aux knd
        (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
        ((Node (sourcenode c'),kind c',Node (targetnode c'))#csx) (?e#es)"
        by simp
      moreover
      from list `cs = c' # cs'`
      have "list_all2 
        (\<lambda>c c'. c' = (Node (sourcenode c), kind c, Node (targetnode c))) cs 
        ((Node (sourcenode c'),kind c',Node (targetnode c'))#csx)"
        by simp
      moreover
      from path `m = sourcenode a` 
        `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit ?e`
      have "CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (Node m) (?e#es) (Node m')" by(fastforce intro:CFGExit.Cons_path)
      ultimately show ?case using `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` by blast
    qed }
  hence lift_valid_path:"\<And>m as m'. \<lbrakk>m -as\<rightarrow>\<^sub>\<surd>* m'; m \<noteq> Entry \<or> m' \<noteq> Exit\<rbrakk> 
    \<Longrightarrow> \<exists>es. CFG.CFG.valid_path' src trg knd
    (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
    (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
    (Node m) es (Node m')"
    by(fastforce simp:vp_def valid_path_def CFGExit.vp_def CFGExit.valid_path_def)
  show ?thesis
  proof
    fix n assume "CFG.CFG.valid_node src trg
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) n"
    hence "((n = NewEntry) \<or> n = NewExit) \<or> (\<exists>m. n = Node m \<and> valid_node m)"
      by(auto elim:lift_valid_edge.cases simp:CFGExit.valid_node_def)
    thus "\<exists>as. CFG.CFG.valid_path' src trg knd
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
      (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
      NewEntry as n" apply -
    proof(erule disjE)+
      assume "n = NewEntry" 
      hence "CFG.CFG.valid_path' src trg knd
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
        NewEntry [] n"
        by(fastforce intro:CFGExit.empty_path 
          simp:CFGExit.vp_def CFGExit.valid_path_def)
      thus ?thesis by blast
    next
      assume "n = NewExit"
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
        (NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Entry_Exit_edge)
      hence "CFG.CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        NewEntry [(NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)] NewExit"
        by(fastforce dest:CFGExit.path_edge)
      with `n = NewExit` have "CFG.CFG.valid_path' src trg knd
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
        NewEntry [(NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)] n"
        by(fastforce simp:CFGExit.vp_def CFGExit.valid_path_def)
      thus ?thesis by blast
    next
      assume "\<exists>m. n = Node m \<and> valid_node m"
      then obtain m where "n = Node m" and "valid_node m" by blast
      from `valid_node m`
      show ?thesis
      proof(cases m rule:valid_node_cases)
        case Entry
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)" by(fastforce intro:lve_Entry_edge)
        with `m = Entry` `n = Node m` have "CFG.CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          NewEntry [(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)] n"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        thus ?thesis by(fastforce simp:CFGExit.vp_def CFGExit.valid_path_def)
      next
        case Exit
        from inner obtain ax where "valid_edge ax" and "intra_kind (kind ax)"
          and "inner_node (sourcenode ax)"
          and "targetnode ax = Exit" by(erule inner_node_Exit_edge)
        hence "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node (sourcenode ax),kind ax,Node Exit)"
          by(auto intro:lift_valid_edge.lve_edge simp:inner_node_def)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node (sourcenode ax)) [(Node (sourcenode ax),kind ax,Node Exit)] 
          (Node Exit)"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        with `intra_kind (kind ax)`
        have slp_edge:"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (Node (sourcenode ax)) [(Node (sourcenode ax),kind ax,Node Exit)] 
          (Node Exit)"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def 
            intra_kind_def)
        have "sourcenode ax \<noteq> Exit"
        proof
          assume "sourcenode ax = Exit"
          with `valid_edge ax` show False by(rule Exit_source)
        qed
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)" by(fastforce intro:lve_Entry_edge)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (NewEntry) [(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)] (Node Entry)"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        hence slp_edge':"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (NewEntry) [(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)] (Node Entry)"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def)
        from `inner_node (sourcenode ax)` have "valid_node (sourcenode ax)"
          by(rule inner_is_valid)
        then obtain asx where "Entry -asx\<rightarrow>\<^sub>\<surd>* sourcenode ax"
          by(fastforce dest:Entry_path)
        with `sourcenode ax \<noteq> Exit`
        have "\<exists>es. CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node Entry) es (Node (sourcenode ax))"
          by(fastforce intro:lift_valid_path)
        then obtain es where "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node Entry) es (Node (sourcenode ax))" by blast
        with slp_edge have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) 
          (Node Entry) (es@[(Node (sourcenode ax),kind ax,Node Exit)]) (Node Exit)"
          by -(rule CFGExit.vp_slp_Append)
        with slp_edge' have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) NewEntry
          ([(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)]@
          (es@[(Node (sourcenode ax),kind ax,Node Exit)])) (Node Exit)"
          by(rule CFGExit.slp_vp_Append)
        with `m = Exit` `n = Node m` show ?thesis by simp blast
      next
        case inner
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)" by(fastforce intro:lve_Entry_edge)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (NewEntry) [(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)] (Node Entry)"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        hence slp_edge:"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (NewEntry) [(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)] (Node Entry)"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def)
        from `valid_node m` obtain as where "Entry -as\<rightarrow>\<^sub>\<surd>* m"
          by(fastforce dest:Entry_path)
        with `inner_node m`
        have "\<exists>es. CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node Entry) es (Node m)"
          by(fastforce intro:lift_valid_path simp:inner_node_def)
        then obtain es where "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node Entry) es (Node m)" by blast
        with slp_edge have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) NewEntry ([(NewEntry,(\<lambda>s. True)\<^sub>\<surd>,Node Entry)]@es) (Node m)"
          by(rule CFGExit.slp_vp_Append)
        with `n = Node m` show ?thesis by simp blast
      qed
    qed
  next
    fix n assume "CFG.CFG.valid_node src trg
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) n"
    hence "((n = NewEntry) \<or> n = NewExit) \<or> (\<exists>m. n = Node m \<and> valid_node m)"
      by(auto elim:lift_valid_edge.cases simp:CFGExit.valid_node_def)
    thus "\<exists>as. CFG.CFG.valid_path' src trg knd
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
      (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
      n as NewExit" apply -
    proof(erule disjE)+
      assume "n = NewEntry"
      have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
        (NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Entry_Exit_edge)
      hence "CFG.CFG.path src trg
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        NewEntry [(NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)] NewExit"
        by(fastforce dest:CFGExit.path_edge)
      with `n = NewEntry` have "CFG.CFG.valid_path' src trg knd
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
        n [(NewEntry,(\<lambda>s. False)\<^sub>\<surd>,NewExit)] NewExit"
        by(fastforce simp:CFGExit.vp_def CFGExit.valid_path_def)
      thus ?thesis by blast
    next
      assume "n = NewExit"
      hence "CFG.CFG.valid_path' src trg knd
        (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
        (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind)
        n [] NewExit"
        by(fastforce intro:CFGExit.empty_path 
          simp:CFGExit.vp_def CFGExit.valid_path_def)
      thus ?thesis by blast
    next
      assume "\<exists>m. n = Node m \<and> valid_node m"
      then obtain m where "n = Node m" and "valid_node m" by blast
      from `valid_node m`
      show ?thesis
      proof(cases m rule:valid_node_cases)
        case Entry
        from inner obtain ax where "valid_edge ax" and "intra_kind (kind ax)"
          and "inner_node (targetnode ax)" and "sourcenode ax = Entry" 
          by(erule inner_node_Entry_edge)
        hence "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node Entry,kind ax,Node (targetnode ax))"
          by(auto intro:lift_valid_edge.lve_edge simp:inner_node_def)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node Entry) [(Node Entry,kind ax,Node (targetnode ax))] 
          (Node (targetnode ax))"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        with `intra_kind (kind ax)`
        have slp_edge:"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (Node Entry) [(Node Entry,kind ax,Node (targetnode ax))] 
          (Node (targetnode ax))"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def 
            intra_kind_def)
        have "targetnode ax \<noteq> Entry"
        proof
          assume "targetnode ax = Entry"
          with `valid_edge ax` show False by(rule Entry_target)
        qed
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Exit_edge)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node Exit) [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)] NewExit"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        hence slp_edge':"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (Node Exit) [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)] NewExit"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def)
        from `inner_node (targetnode ax)` have "valid_node (targetnode ax)"
          by(rule inner_is_valid)
        then obtain asx where "targetnode ax -asx\<rightarrow>\<^sub>\<surd>* Exit"
          by(fastforce dest:Exit_path)
        with `targetnode ax \<noteq> Entry`
        have "\<exists>es. CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node (targetnode ax)) es (Node Exit)"
          by(fastforce intro:lift_valid_path)
        then obtain es where "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node (targetnode ax)) es (Node Exit)" by blast
        with slp_edge have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) 
          (Node Entry) ([(Node Entry,kind ax,Node (targetnode ax))]@es) (Node Exit)"
          by(rule CFGExit.slp_vp_Append)
        with slp_edge' have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node Entry)
          (([(Node Entry,kind ax,Node (targetnode ax))]@es)@
          [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)]) NewExit"
          by -(rule CFGExit.vp_slp_Append)
        with `m = Entry` `n = Node m` show ?thesis by simp blast
      next
        case Exit
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Exit_edge)
        with `m = Exit` `n = Node m` have "CFG.CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          n [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)] NewExit"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        thus ?thesis by(fastforce simp:CFGExit.vp_def CFGExit.valid_path_def)
      next
        case inner
        have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit
          (Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)" by(fastforce intro:lve_Exit_edge)
        hence "CFG.path src trg
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (Node Exit) [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)] NewExit"
          by(fastforce intro:CFGExit.Cons_path CFGExit.empty_path
                       simp:CFGExit.valid_node_def)
        hence slp_edge:"CFG.CFG.same_level_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind)
          (Node Exit) [(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)] NewExit"
          by(fastforce simp:CFGExit.slp_def CFGExit.same_level_path_def)
        from `valid_node m` obtain as where "m -as\<rightarrow>\<^sub>\<surd>* Exit"
          by(fastforce dest:Exit_path)
        with `inner_node m`
        have "\<exists>es. CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node m) es (Node Exit)"
          by(fastforce intro:lift_valid_path simp:inner_node_def)
        then obtain es where "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node m) es (Node Exit)" by blast
        with slp_edge have "CFG.CFG.valid_path' src trg knd
          (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit)
          (lift_get_return_edges get_return_edges valid_edge sourcenode 
          targetnode kind) (Node m) (es@[(Node Exit,(\<lambda>s. True)\<^sub>\<surd>,NewExit)]) NewExit"
          by -(rule CFGExit.vp_slp_Append)
        with `n = Node m` show ?thesis by simp blast
      qed
    qed
  next
    fix n n'
    assume method_exit1:"CFGExit.CFGExit.method_exit src knd
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewExit n"
      and method_exit2:"CFGExit.CFGExit.method_exit src knd
      (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewExit n'"
      and lift_eq:"lift_get_proc get_proc Main n = lift_get_proc get_proc Main n'"
    from method_exit1 show "n = n'"
    proof(rule CFGExit.method_exit_cases)
      assume "n = NewExit"
      from method_exit2 show ?thesis
      proof(rule CFGExit.method_exit_cases)
        assume "n' = NewExit"
        with `n = NewExit` show ?thesis by simp
      next
        fix a Q f p
        assume "n' = src a"
          and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
          and "knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        hence "lift_get_proc get_proc Main (src a) = p"
          by -(rule CFGExit.get_proc_return)
        with CFGExit.get_proc_Exit lift_eq `n' = src a` `n = NewExit`
        have "p = Main" by simp
        with `knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "knd a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a`
        have False by(rule CFGExit.Main_no_return_source)
        thus ?thesis by simp
      qed
    next
      fix a Q f p
      assume "n = src a"
        and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
        and "knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      then obtain x where "valid_edge x" and "src a = Node (sourcenode x)"
        and "kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        by(fastforce elim:lift_valid_edge.cases)
      hence "method_exit (sourcenode x)" by(fastforce simp:method_exit_def)
      from method_exit2 show ?thesis
      proof(rule CFGExit.method_exit_cases)
        assume "n' = NewExit"
        from `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a`
          `knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
        have "lift_get_proc get_proc Main (src a) = p"
          by -(rule CFGExit.get_proc_return)
        with CFGExit.get_proc_Exit lift_eq `n = src a` `n' = NewExit`
        have "p = Main" by simp
        with `knd a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "knd a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with `lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a`
        have False by(rule CFGExit.Main_no_return_source)
        thus ?thesis by simp
      next
        fix a' Q' f' p'
        assume "n' = src a'"
          and "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a'"
          and "knd a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'"
        then obtain x' where "valid_edge x'" and "src a' = Node (sourcenode x')"
          and "kind x' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'"
          by(fastforce elim:lift_valid_edge.cases)
        hence "method_exit (sourcenode x')" by(fastforce simp:method_exit_def)
        with `method_exit (sourcenode x)` lift_eq `n = src a` `n' = src a'`
          `src a = Node (sourcenode x)` `src a' = Node (sourcenode x')`
        have "sourcenode x = sourcenode x'" by(fastforce intro:method_exit_unique)
        with `src a = Node (sourcenode x)` `src a' = Node (sourcenode x')`
          `n = src a` `n' = src a'`
        show ?thesis by simp
      qed
    qed
  qed
qed


lemma lift_SDG:
  assumes SDG:"SDG sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and inner:"CFGExit.inner_node sourcenode targetnode valid_edge Entry Exit nx"
  shows "SDG src trg knd
  (lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit) NewEntry
  (lift_get_proc get_proc Main) 
  (lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind) 
  procs Main NewExit (lift_Def Def Entry Exit H L) (lift_Use Use Entry Exit H L)
  (lift_ParamDefs ParamDefs) (lift_ParamUses ParamUses)"
proof -
  interpret SDG sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule SDG)
  have wf:"CFGExit_wf sourcenode targetnode kind valid_edge Entry get_proc
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
    by(unfold_locales)
  have pd:"Postdomination sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit"
    by(unfold_locales)
  interpret wf':CFGExit_wf src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main"
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
    procs Main NewExit "lift_Def Def Entry Exit H L" "lift_Use Use Entry Exit H L"
    "lift_ParamDefs ParamDefs" "lift_ParamUses ParamUses"
    by(fastforce intro:lift_CFGExit_wf wf pd)
  interpret pd':Postdomination src trg knd
    "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit" NewEntry
    "lift_get_proc get_proc Main"
    "lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind" 
    procs Main NewExit
    by(fastforce intro:lift_Postdomination wf pd inner)
  show ?thesis by(unfold_locales)
qed


subsubsection {* Low-deterministic security via the lifted graph *}

lemma Lift_NonInterferenceGraph:
  fixes valid_edge and sourcenode and targetnode and kind and Entry and Exit
  and get_proc and get_return_edges and procs and Main
  and Def and Use and ParamDefs and ParamUses and H and L
  defines lve:"lve \<equiv> lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit"
  and lget_proc:"lget_proc \<equiv> lift_get_proc get_proc Main"
  and lget_return_edges:"lget_return_edges \<equiv> 
  lift_get_return_edges get_return_edges valid_edge sourcenode targetnode kind"
  and lDef:"lDef \<equiv> lift_Def Def Entry Exit H L" 
  and lUse:"lUse \<equiv> lift_Use Use Entry Exit H L"
  and lParamDefs:"lParamDefs \<equiv> lift_ParamDefs ParamDefs"
  and lParamUses:"lParamUses \<equiv> lift_ParamUses ParamUses"
  assumes SDG:"SDG sourcenode targetnode kind valid_edge Entry get_proc 
  get_return_edges procs Main Exit Def Use ParamDefs ParamUses"
  and inner:"CFGExit.inner_node sourcenode targetnode valid_edge Entry Exit nx"
  and "H \<inter> L = {}" and "H \<union> L = UNIV"
  shows "NonInterferenceInterGraph src trg knd lve NewEntry lget_proc 
  lget_return_edges procs Main NewExit lDef lUse lParamDefs lParamUses H L 
  (Node Entry) (Node Exit)"
proof -
  interpret SDG sourcenode targetnode kind valid_edge Entry get_proc 
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses
    by(rule SDG)
  interpret SDG':SDG src trg knd lve NewEntry lget_proc lget_return_edges
    procs Main NewExit lDef lUse lParamDefs lParamUses
    by(fastforce intro:lift_SDG SDG inner simp:lve lget_proc lget_return_edges lDef
                      lUse lParamDefs lParamUses)
  show ?thesis
  proof
    fix a assume "lve a" and "src a = NewEntry"
    thus "trg a = NewExit \<or> trg a = Node Entry"
      by(fastforce elim:lift_valid_edge.cases simp:lve)
  next
    show "\<exists>a. lve a \<and> src a = NewEntry \<and> trg a = Node Entry \<and> knd a = (\<lambda>s. True)\<^sub>\<surd>"
      by(fastforce intro:lve_Entry_edge simp:lve)
  next
    fix a assume "lve a" and "trg a = Node Entry"
    from `lve a` 
    have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      by(simp add:lve)
    from this `trg a = Node Entry`
    show "src a = NewEntry"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` 
        `trg e = Node Entry`
      have "targetnode a = Entry" by simp
      with `valid_edge a` have False by(rule Entry_target)
      thus ?case by simp
    qed simp_all
  next
    fix a assume "lve a" and "trg a = NewExit"
    thus "src a = NewEntry \<or> src a = Node Exit"
      by(fastforce elim:lift_valid_edge.cases simp:lve)
  next
    show "\<exists>a. lve a \<and> src a = Node Exit \<and> trg a = NewExit \<and> knd a = (\<lambda>s. True)\<^sub>\<surd>"
      by(fastforce intro:lve_Exit_edge simp:lve)
  next
    fix a assume "lve a" and "src a = Node Exit"
    from `lve a` 
    have "lift_valid_edge valid_edge sourcenode targetnode kind Entry Exit a"
      by(simp add:lve)
    from this `src a = Node Exit`
    show "trg a = NewExit"
    proof(induct rule:lift_valid_edge.induct)
      case (lve_edge a e)
      from `e = (Node (sourcenode a), kind a, Node (targetnode a))` 
        `src e = Node Exit`
      have "sourcenode a = Exit" by simp
      with `valid_edge a` have False by(rule Exit_source)
      thus ?case by simp
    qed simp_all
  next
    from lDef show "lDef (Node Entry) = H"
      by(fastforce elim:lift_Def_set.cases intro:lift_Def_High)
  next
    from Entry_noteq_Exit lUse show "lUse (Node Entry) = H"
      by(fastforce elim:lift_Use_set.cases intro:lift_Use_High)
  next
    from Entry_noteq_Exit lUse show "lUse (Node Exit) = L"
      by(fastforce elim:lift_Use_set.cases intro:lift_Use_Low)
  next
    from `H \<inter> L = {}` show "H \<inter> L = {}" .
  next
    from `H \<union> L = UNIV` show "H \<union> L = UNIV" .
  qed
qed

end



