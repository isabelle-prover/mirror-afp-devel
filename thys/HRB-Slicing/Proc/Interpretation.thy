header {* \isaheader{Instantiate CFG locales with Proc CFG} *}

theory Interpretation imports WellFormProgs "../StaticInter/CFGExit" begin

subsection {* Lifting of the basic definitions *}

abbreviation sourcenode :: "edge \<Rightarrow> node"
  where "sourcenode e \<equiv> fst e"

abbreviation targetnode :: "edge \<Rightarrow> node"
  where "targetnode e \<equiv> snd(snd e)"

abbreviation kind :: "edge \<Rightarrow> (lift_var,val) edge_kind"
  where "kind e \<equiv> fst(snd e)"


definition valid_edge :: "wf_prog \<Rightarrow> edge \<Rightarrow> bool"
  where "valid_edge wfp a \<equiv> let (prog,procs) = Rep_wf_prog wfp in
  prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"


definition get_return_edges :: "wf_prog \<Rightarrow> edge \<Rightarrow> edge set"
  where "get_return_edges wfp a \<equiv> 
  case kind a of Q\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> 
    let (i,l) = (THE (i,l). \<exists>es. fs = set_params i (Suc l) es) in
    (case i of 0 \<Rightarrow> {a'. valid_edge wfp a' \<and> (\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f') \<and>
                         targetnode a' = (Main,Label (Suc l))}
         | Suc n \<Rightarrow> let (prog,procs) = Rep_wf_prog wfp in
          (if (n < length procs) then {a'. valid_edge wfp a' \<and> 
          (\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f') \<and> targetnode a' = (fst (procs!n),Label (Suc l))}
   else {}))
                   | _ \<Rightarrow> {}"


lemma get_return_edges_non_call_empty:
  "\<forall>Q p fs. kind a \<noteq> Q\<hookrightarrow>\<^bsub>p\<^esub>fs \<Longrightarrow> get_return_edges wfp a = {}"
  by(cases "kind a",auto simp:get_return_edges_def)



lemma call_has_return_edge_Main:
  assumes "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "fs = set_params 0 (Suc l) es"
  obtains a' where "valid_edge wfp a'" and "\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
  and "targetnode a' = (Main,Label (Suc l))"
proof(atomize_elim)
  from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain prog procs where "Rep_wf_prog wfp = (prog,procs)"
    and "prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by(fastsimp simp:valid_edge_def)
  with `fs = set_params 0 (Suc l) es`
  obtain es' rets n' ins outs c where "prog \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'"
    and rest:"(p,ins,outs,c) \<in> set procs"
    "distinct rets" "length rets = length outs" "length es' + 2 = length ins"
    by(fastsimp elim!:PCFG.cases dest:fun_cong)
  from `prog \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'` obtain l' where "n' = Label (Suc l)"
    by(fastsimp dest:Proc_CFG_Call_Labels)
  with `prog \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'` rest
  have "prog,procs \<turnstile> (p,Exit) -(correct_return 0 (Suc l))\<^bsub>p\<^esub>\<hookleftarrow>
                 (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label (Suc l))"
    by(fastsimp intro:MainReturn)
  with `Rep_wf_prog wfp = (prog,procs)`
  show "\<exists>a'. valid_edge wfp a' \<and> (\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f') \<and> 
    targetnode a' = (Main,Label (Suc l))"
    by(fastsimp simp:valid_edge_def)
qed


lemma call_has_return_edge_Proc:
  assumes "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "fs = set_params (Suc i) (Suc l) es" 
  obtains a' where "valid_edge wfp a'" and "\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
  and "targetnode a' = (fst(snd (Rep_wf_prog wfp)!i),Label (Suc l))"
proof(atomize_elim)
  from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain prog procs where "Rep_wf_prog wfp = (prog,procs)"
    and "prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by(fastsimp simp:valid_edge_def)
  from `prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a` 
    `Rep_wf_prog wfp = (prog,procs)` `fs = set_params (Suc i) (Suc l) es`
  obtain es' rets l' ins outs c ps p' ins' outs' c' esx retsx
    where "c \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l'"
    and rest:"procs!i = (p',ins,outs,c)" "i < length procs" 
    "(p,ins',outs',c') \<in> set procs" "containsCall procs prog ps p' esx retsx"
    "distinct rets" "length rets = length outs'" "length es' + 2 = length ins'"
    by(fastsimp elim!:PCFG.cases dest:fun_cong)
  from `c \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l'` have "l' = Suc l"
    by(fastsimp dest:Proc_CFG_Call_Labels)
  with `c \<turnstile> Label l -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l'` rest
  have "prog,procs \<turnstile> (p,Exit) -(correct_return (Suc i) (Suc l))\<^bsub>p\<^esub>\<hookleftarrow>
                  (\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs'))\<rightarrow> (p',Label (Suc l))"
    by(fastsimp intro:ProcReturn)
  with `i < length procs` `procs!i = (p',ins,outs,c)` `Rep_wf_prog wfp = (prog,procs)`
  show "\<exists>a'. valid_edge wfp a' \<and> (\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f') \<and>
              targetnode a' = (fst(snd (Rep_wf_prog wfp)!i),Label (Suc l))"
    by(fastsimp simp:valid_edge_def)
qed


lemma get_return_edges_call_nonempty:
  assumes "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "get_return_edges wfp a \<noteq> {}"
proof -
  from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain prog procs where "Rep_wf_prog wfp = (prog,procs)"
    and edge:"prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
    by(fastsimp simp:valid_edge_def)
  then obtain i l es where "fs = set_params i (Suc l) es" and "i < Suc (length procs)"
    by(fastsimp dest:PCFG_CallEdge_set_params)
  with edge have "(THE (i',l'). \<exists>es'. fs = set_params i' (Suc l') es') = (i,l)"
    by(fastsimp intro:PCFG_CallEdge_THE_set_params)
  show ?thesis
  proof(cases i)
    case 0
    with `fs = set_params i (Suc l) es` have "fs = set_params 0 (Suc l) es"
      by simp
    with `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain a' where "valid_edge wfp a'" and "\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
      and "targetnode a' = (Main,Label (Suc l))"
      by(erule call_has_return_edge_Main)
    with `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `i = 0`
      `(THE (i',l'). \<exists>es'. fs = set_params i' (Suc l') es') = (i,l)`
    show ?thesis
      apply(cases "kind a",auto simp:get_return_edges_def valid_edge_def)
      apply(rule_tac x="fst(sourcenode a')" in exI)
      apply(rule_tac x="snd(sourcenode a')" in exI)
      apply(rule_tac x="kind a'" in exI)
      by clarsimp
  next
    case (Suc j)
    with `fs = set_params i (Suc l) es` have "fs = set_params (Suc j) (Suc l) es"
      by simp
    with `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain a' where "valid_edge wfp a'" and "\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
      and "targetnode a' = (fst(snd (Rep_wf_prog wfp)!j),Label (Suc l))"
      by(erule call_has_return_edge_Proc)
    with `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `i < Suc (length procs)` `i = Suc j`
      `(THE (i',l'). \<exists>es'. fs = set_params i' (Suc l') es') = (i,l)`
      `Rep_wf_prog wfp = (prog,procs)`
    show ?thesis
      apply(cases "kind a",auto simp:get_return_edges_def valid_edge_def Let_def)
      apply(rule_tac x="fst(sourcenode a')" in exI)
      apply(rule_tac x="snd(sourcenode a')" in exI)
      apply(rule_tac x="kind a'" in exI)
      by clarsimp
  qed
qed



lemma only_return_edges_in_get_return_edges:
  "\<lbrakk>valid_edge wfp a; kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges wfp a\<rbrakk>
  \<Longrightarrow> \<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
apply(cases "kind a") apply(auto simp:get_return_edges_def)
by(case_tac x)(auto simp:Let_def split:split_if_asm)


abbreviation lift_procs :: "wf_prog \<Rightarrow> (pname \<times> lift_var list \<times> lift_var list) list"
  where "lift_procs wfp \<equiv> let (prog,procs) = Rep_wf_prog wfp in
  map (\<lambda>x. (fst x,fst(snd x),fst(snd(snd x)))) procs"


subsection {* Instatiation of the @{text CFG} locale *}


interpretation ProcCFG:
  CFG sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastsimp simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastsimp intro:wf_wf_prog)
  show "CFG sourcenode targetnode kind (valid_edge wfp) (Main, Entry)
    get_proc (get_return_edges wfp) (lift_procs wfp) Main"
  proof
    fix a assume "valid_edge wfp a" and "targetnode a = (Main, Entry)"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    show "get_proc (Main, Entry) = Main" by simp
  next
    fix a Q p fs 
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "sourcenode a = (Main, Entry)"
    thus False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a a' 
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "sourcenode a = sourcenode a'" and "targetnode a = targetnode a'"
    with wf show "a = a'"
      by(cases a,cases a',auto dest:Proc_CFG_edge_det simp:valid_edge_def)
  next
    fix a Q f
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>Main\<^esub>f"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a Q' f'
    assume "valid_edge wfp a" and "kind a = Q'\<^bsub>Main\<^esub>\<hookleftarrow>f'"
    from this wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    fix a Q p fs
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "\<exists>ins outs. (p, ins, outs) \<in> set (lift_procs wfp)"
      apply(auto simp:valid_edge_def) apply(erule PCFG.cases) apply auto
         apply(fastsimp dest:Proc_CFG_IEdge_intra_kind simp:intra_kind_def)
	apply(fastsimp dest:Proc_CFG_IEdge_intra_kind simp:intra_kind_def)
       apply(rule_tac x="ins" in exI) apply(rule_tac x="outs" in exI)
       apply(rule_tac x="(p,ins,outs,c)" in image_eqI) apply auto
      apply(rule_tac x="ins'" in exI) apply(rule_tac x="outs'" in exI)
      apply(rule_tac x="(p,ins',outs',c')" in image_eqI) by(auto simp:set_conv_nth)
  next
    fix a assume "valid_edge wfp a" and "intra_kind (kind a)"
    thus "get_proc (sourcenode a) = get_proc (targetnode a)"
      by(auto elim:PCFG.cases simp:valid_edge_def intra_kind_def)
  next
    fix a Q p fs
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "get_proc (targetnode a) = p" by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
    thus "get_proc (sourcenode a) = p" by(auto elim:PCFG.cases simp:valid_edge_def) 
  next
    fix a Q p fs
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    show "\<forall>a'. valid_edge wfp a' \<and> targetnode a' = targetnode a \<longrightarrow>
      (\<exists>Qx fsx. kind a' = Qx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' ins outs c)
      from `\<lambda>s. True\<hookrightarrow>\<^bsub>p'\<^esub>set_params 0 (Suc l) es = kind a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "targetnode a' = (p', Entry)"
	hence "\<exists>Qx fsx. kind a' = Qx\<hookrightarrow>\<^bsub>p\<^esub>fsx"
	  by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p',Entry) = targetnode a` show ?case by simp
    next
      case (ProcCall i px ins outs c l p' es rets l' ins' outs' c')
      from `\<lambda>s. True\<hookrightarrow>\<^bsub>p'\<^esub>set_params (Suc i) (Suc l) es = kind a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "targetnode a' = (p', Entry)"
	hence "\<exists>Qx fsx. kind a' = Qx\<hookrightarrow>\<^bsub>p\<^esub>fsx" 
	  by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Entry) = targetnode a` show ?case by simp
    qed auto
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
    show "\<forall>a'. valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<longrightarrow>
      (\<exists>Qx fx. kind a' = Qx\<^bsub>p\<^esub>\<hookleftarrow>fx)"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' ins outs c)
      from `correct_return 0 l'\<^bsub>p'\<^esub>\<hookleftarrow> \<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs) = 
	kind a` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "sourcenode a' = (p', Exit)"
	hence "\<exists>Qx fx. kind a' = Qx\<^bsub>p\<^esub>\<hookleftarrow>fx" 
	  by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Exit) = sourcenode a` show ?case by simp
    next
      case (ProcReturn i px ins outs c l p' es rets l' ins' outs' c')
      from `correct_return (Suc i) l'\<^bsub>p'\<^esub>\<hookleftarrow>	\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs') =
	kind a` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have [simp]:"p' = p" by simp
      { fix a' assume "valid_edge wfp a'" and "sourcenode a' = (p', Exit)"
	hence "\<exists>Qx fx. kind a' = Qx\<^bsub>p\<^esub>\<hookleftarrow>fx" 
	  by(auto elim:PCFG.cases simp:valid_edge_def) }
      with `(p', Exit) = sourcenode a` show ?case by simp
    qed auto
  next
    fix a Q p fs
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
    thus "get_return_edges wfp a \<noteq> {}" by(rule get_return_edges_call_nonempty)
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    thus "valid_edge wfp a'"
      by(cases "kind a")
    (auto simp:get_return_edges_def,case_tac x,auto simp:Let_def split:split_if_asm)
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    thus "\<exists>Q p fs. kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
      by(cases "kind a")(auto simp:get_return_edges_def)
  next
    fix a Q p fs a'
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "a' \<in> get_return_edges wfp a"
    thus "\<exists>Q' f'. kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" by(rule only_return_edges_in_get_return_edges)
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
    show "\<exists>!a'. valid_edge wfp a' \<and> (\<exists>Q fs. kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
      a \<in> get_return_edges wfp a'"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainReturn l px es rets l' ins outs c)
      from `correct_return 0 l'\<^bsub>px\<^esub>\<hookleftarrow> \<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs) =
	kind a` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have [simp]:"px = p" by simp
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'` have "l' = Suc l"
	by(fastsimp dest:Proc_CFG_Call_Labels)
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'`
	`(px, ins, outs, c) \<in> set procs`	 `distinct rets` `length rets = length outs`
	`length es + 2 = length ins`
      have "prog,procs \<turnstile> (p,Exit) -(correct_return 0 l')\<^bsub>p\<^esub>\<hookleftarrow>
	(\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs))\<rightarrow> (Main,Label l')"
	by(fastsimp intro:PCFG.MainReturn)
      with `(px, Exit) = sourcenode a` `(Main, Label l') = targetnode a`
	`correct_return 0 l'\<^bsub>px\<^esub>\<hookleftarrow>\<lambda>cf cf'. cf'(map Loc rets [:=] map cf outs) = kind a`
      have edge:"prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a" by simp
      from `prog \<turnstile> Label l -CEdge (px, es, rets)\<rightarrow>\<^isub>p Label l'`
	`(px, ins, outs, c) \<in> set procs` `distinct rets` `length rets = length outs`
	`length es + 2 = length ins`
      have edge':"prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 (Suc l) es\<rightarrow> 
	(p,Entry)" by(fastsimp intro:MainCall)
      show ?case
      proof(rule ex_ex1I)
	from edge'
	have "(THE (i',l'). \<exists>es'. set_params 0 (Suc l) es = 
	                          set_params i' (Suc l') es') = (0,l)"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params)
	with edge edge' `(Main, Label l') = targetnode a` 
	  `l' = Suc l` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
	show "\<exists>a'. valid_edge wfp a' \<and>
          (\<exists>Q fs. kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
	  by(fastsimp simp:valid_edge_def get_return_edges_def)
      next
	fix a' a''
	assume "valid_edge wfp a' \<and>
          (\<exists>Q fs. kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
	  and "valid_edge wfp a'' \<and>
          (\<exists>Q fs. kind a'' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a''"
	then obtain Q fs Q' fs' where "valid_edge wfp a'"
	  and "kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a \<in> get_return_edges wfp a'"
	  and "valid_edge wfp a''" and "kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
	  and "a \<in> get_return_edges wfp a''" by blast
	from `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
	obtain i lx es where "fs = set_params i (Suc lx) es" 
	  and "i < Suc(length procs)"
	  by(fastsimp dest:PCFG_CallEdge_set_params simp:valid_edge_def)
	from `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `fs = set_params i (Suc lx) es`
	have the:"(THE (i'',l''). \<exists>es''. fs = set_params i'' (Suc l'') es'') = (i,lx)"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params simp:valid_edge_def)
	have nodes:"sourcenode a' = (Main,Label l) \<and> targetnode a' = (p,Entry)"
	proof(cases i)
	  case 0
	  with `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	    `a \<in> get_return_edges wfp a'` edge the
	    `fs = set_params i (Suc lx) es` `(Main, Label l') = targetnode a` wf
	  obtain es where "prog,procs \<turnstile> sourcenode a' -Q\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 l' es\<rightarrow> 
	    targetnode a'" by(auto simp:valid_edge_def get_return_edges_def)
	  with `l' = Suc l` show ?thesis by(fastsimp elim:PCFG.cases dest:fun_cong)
	next
	  case (Suc j)
	  with `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `a \<in> get_return_edges wfp a'`
	    edge the `fs = set_params i (Suc lx) es` 
	    `(Main, Label l') = targetnode a` wf have False
	    by(auto simp:valid_edge_def get_return_edges_def)
	  (case_tac "procs ! j",auto simp:Let_def split:split_if_asm)
	  thus ?thesis by simp
	qed
	from `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
	obtain i' lx' es' where "fs' = set_params i' (Suc lx') es'" 
	  and "i' < Suc(length procs)"
	  by(fastsimp dest:PCFG_CallEdge_set_params simp:valid_edge_def)
	from `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	  `fs' = set_params i' (Suc lx') es'`
	have the':"(THE (i'',l''). \<exists>es''. fs' = set_params i'' (Suc l'') es'') = 
	  (i',lx')"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params simp:valid_edge_def)
	have nodes':"sourcenode a'' = (Main,Label l) \<and> targetnode a'' = (p,Entry)"
	proof(cases i')
	  case 0
	  with `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	    `a \<in> get_return_edges wfp a''` edge the'
	    `fs' = set_params i' (Suc lx') es'` `(Main, Label l') = targetnode a` wf
	  obtain es where "prog,procs \<turnstile> sourcenode a'' -Q'\<hookrightarrow>\<^bsub>p\<^esub>set_params 0 l' es'\<rightarrow> 
	    targetnode a''" by(auto simp:valid_edge_def get_return_edges_def)
	  with `l' = Suc l` show ?thesis by(fastsimp elim:PCFG.cases dest:fun_cong)
	next
	  case (Suc j)
	  with `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	    `a \<in> get_return_edges wfp a''` edge the'
	    `fs' = set_params i' (Suc lx') es'` `(Main, Label l') = targetnode a` wf
	  have False
	    by(auto simp:valid_edge_def get_return_edges_def)
	  (case_tac "procs ! j",auto simp:Let_def split:split_if_asm)
	  thus ?thesis by simp
	qed
	with nodes `valid_edge wfp a'` `valid_edge wfp a''` wf
	have "kind a' = kind a''"
	  by(fastsimp dest:Proc_CFG_edge_det simp:valid_edge_def)
	with nodes nodes' show "a' = a''" by(cases a',cases a'',auto)
      qed
    next
      case (ProcReturn i p' ins outs c l px esx retsx l' ins' outs' c' ps es rets)
      from `correct_return (Suc i) l'\<^bsub>px\<^esub>\<hookleftarrow> \<lambda>cf cf'. cf'(map Loc retsx [:=] map cf outs')
	= kind a` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have [simp]:"px = p" by simp
      from `c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^isub>p Label l'` have "l' = Suc l"
	by(fastsimp dest:Proc_CFG_Call_Labels)
      from `i < length procs` `procs ! i = (p',ins,outs,c)`
	`c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^isub>p Label l'` 
	`(px, ins', outs', c') \<in> set procs` `containsCall procs prog ps p' es rets`
	`distinct retsx` `length retsx = length outs'` `length esx + 2 = length ins'`
      have "prog,procs \<turnstile> (p,Exit) -(correct_return (Suc i) l')\<^bsub>p\<^esub>\<hookleftarrow>
	(\<lambda>cf cf'. cf'(map Loc retsx [:=] map cf outs'))\<rightarrow> (p',Label l')"
	by(fastsimp intro:PCFG.ProcReturn)
      with `(px, Exit) = sourcenode a` `(p', Label l') = targetnode a`
	`correct_return (Suc i) l'\<^bsub>px\<^esub>\<hookleftarrow> \<lambda>cf cf'. cf'(map Loc retsx [:=] map cf outs')
	= kind a` have edge:"prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a" by simp
      from `i < length procs` `procs ! i = (p',ins,outs,c)`
	`c \<turnstile> Label l -CEdge (px, esx, retsx)\<rightarrow>\<^isub>p Label l'`
	`(px, ins', outs', c') \<in> set procs` `containsCall procs prog ps p' es rets`
	`distinct retsx` `length retsx = length outs'` `length esx + 2 = length ins'`
      have edge':"prog,procs \<turnstile> (p',Label l) 
	-(\<lambda>s. True)\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc i) (Suc l) esx\<rightarrow> (p,Entry)"	
	by(fastsimp intro:ProcCall)
      show ?case
      proof(rule ex_ex1I)
	from edge'
	have "(THE (i',l'). \<exists>es'. set_params (Suc i) (Suc l) esx = 
	                          set_params i' (Suc l') es') = (Suc i,l)"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params)
	with edge edge' `(p', Label l') = targetnode a` `l' = Suc l`
	  `procs ! i = (p', ins, outs, c)` `i < length procs` `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
	show "\<exists>a'. valid_edge wfp a' \<and>
          (\<exists>Q fs. kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
	  by(fastsimp simp:valid_edge_def get_return_edges_def Let_def)
      next
	fix a' a''
	assume "valid_edge wfp a' \<and>
          (\<exists>Q fs. kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a'"
	  and "valid_edge wfp a'' \<and>
          (\<exists>Q fs. kind a'' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges wfp a''"
	then obtain Q fs Q' fs' where "valid_edge wfp a'"
	  and "kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a \<in> get_return_edges wfp a'"
	  and "valid_edge wfp a''" and "kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
	  and "a \<in> get_return_edges wfp a''" by blast
	from `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
	obtain ix lx es where "fs = set_params ix (Suc lx) es" 
	  and "ix < Suc(length procs)"
	  by(fastsimp dest:PCFG_CallEdge_set_params simp:valid_edge_def)
	from `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	  `fs = set_params ix (Suc lx) es`
	have the:"(THE (i'',l''). 
	  \<exists>es''. fs = set_params i'' (Suc l'') es'') = (ix,lx)"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params simp:valid_edge_def)
	have nodes:"sourcenode a' = (p',Label l) \<and> targetnode a' = (p,Entry)"
	proof(cases ix)
	  case 0
	  with `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	    `a \<in> get_return_edges wfp a'` edge the
	    `fs = set_params ix (Suc lx) es` `(p', Label l') = targetnode a` wf
	    `i < length procs` `procs ! i = (p', ins, outs, c)`
	  have False by(fastsimp simp:valid_edge_def get_return_edges_def)
	  thus ?thesis by simp
	next
	  case (Suc j)
	  with `valid_edge wfp a'` `kind a' = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	    `a \<in> get_return_edges wfp a'` edge the
	    `fs = set_params ix (Suc lx) es` `(p', Label l') = targetnode a` wf
	    `i < length procs` `procs ! i = (p', ins, outs, c)`
	  obtain es where ret_edge:"prog,procs \<turnstile> sourcenode a' 
	    -Q\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc j) l' es\<rightarrow> targetnode a'"
	    and "fst (procs ! j) = p'" and "j < length procs"
	    by(auto simp:valid_edge_def get_return_edges_def Let_def 
	            split:split_if_asm)
	  from wf `i < length procs` `procs ! i = (p', ins, outs, c)` 
	    `fst (procs ! j) = p'` `j < length procs`
	  have [simp]:"i = j" 
	    by(cases "procs ! j",auto dest:well_formed_same_procs_nth_nth)
	  from ret_edge `l' = Suc l` `ix = Suc j` `i < length procs`
	    `procs ! i = (p', ins, outs, c)` wf
	  show ?thesis by(fastsimp elim:PCFG.cases dest:fun_cong)
	qed
	from `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
	obtain ix' lx' es' where "fs' = set_params ix' (Suc lx') es'" 
	  and "ix' < Suc(length procs)"
	  by(fastsimp dest:PCFG_CallEdge_set_params simp:valid_edge_def)
	from `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	  `fs' = set_params ix' (Suc lx') es'`
	have the':"(THE (i'',l''). \<exists>es''. fs' = set_params i'' (Suc l'') es'') = 
	  (ix',lx')"
	  by(fastsimp intro:PCFG_CallEdge_THE_set_params simp:valid_edge_def)
	have nodes':"sourcenode a'' = (p',Label l) \<and> targetnode a'' = (p,Entry)"
	proof(cases ix')
	  case 0
	  with `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	    `a \<in> get_return_edges wfp a''` edge the'
	    `fs' = set_params ix' (Suc lx') es'` `(p', Label l') = targetnode a` wf
	    `i < length procs` `procs ! i = (p', ins, outs, c)`
	  have False by(fastsimp simp:valid_edge_def get_return_edges_def)
	  thus ?thesis by simp
	next
	  case (Suc j)
	  with `valid_edge wfp a''` `kind a'' = Q'\<hookrightarrow>\<^bsub>p\<^esub>fs'` 
	    `a \<in> get_return_edges wfp a''` edge the'
	    `fs' = set_params ix' (Suc lx') es'` `(p', Label l') = targetnode a` wf
	    `i < length procs` `procs ! i = (p', ins, outs, c)`
	  obtain es where ret_edge:"prog,procs \<turnstile> sourcenode a'' 
	    -Q'\<hookrightarrow>\<^bsub>p\<^esub>set_params (Suc j) l' es'\<rightarrow> targetnode a''"
	    and "fst (procs ! j) = p'" and "j < length procs"
	    by(auto simp:valid_edge_def get_return_edges_def Let_def 
	            split:split_if_asm)
	  from wf `i < length procs` `procs ! i = (p', ins, outs, c)` 
	    `fst (procs ! j) = p'` `j < length procs`
	  have [simp]:"i = j" 
	    by(cases "procs ! j",auto dest:well_formed_same_procs_nth_nth)
	  from ret_edge `l' = Suc l` `ix' = Suc j` `i < length procs`
	    `procs ! i = (p', ins, outs, c)` wf
	  show ?thesis by(fastsimp elim:PCFG.cases dest:fun_cong)
	qed
	with nodes `valid_edge wfp a'` `valid_edge wfp a''` wf
	have "kind a' = kind a''"
	  by(fastsimp dest:Proc_CFG_edge_det simp:valid_edge_def)
	with nodes nodes' show "a' = a''" by(cases a',cases a'',auto)
      qed
    qed auto
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    then obtain Q p fs l'
      where "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge wfp a'"
      and disj:"((THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l') \<and>
      targetnode a' = (Main, Label (Suc l'))) \<or>
      (\<exists>j. (THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j,l') \<and>
      targetnode a' = (fst (procs ! j), Label (Suc l')) \<and> j < length procs)"
      apply(cases "kind a") apply(auto simp:valid_edge_def get_return_edges_def)
      by(case_tac x)(fastsimp simp:valid_edge_def Let_def split:split_if_asm)+
    from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges wfp a`
    obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" 
      by(fastsimp dest!:only_return_edges_in_get_return_edges)
    from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have edge:"prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from edge obtain ix lx es where "fs = set_params ix (Suc lx) es" 
      by(fastsimp dest:PCFG_CallEdge_set_params)
    with edge have "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)"
      by(fastsimp intro:PCFG_CallEdge_THE_set_params)
    from disj show "\<exists>a''. valid_edge wfp a'' \<and> 
      sourcenode a'' = targetnode a \<and> targetnode a'' = sourcenode a' \<and> 
      kind a'' = (\<lambda>cf. False)\<^isub>\<surd>"
    proof
      assume "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l') \<and>
	targetnode a' = (Main, Label (Suc l'))"
      hence "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l')"
	and "targetnode a' = (Main, Label (Suc l'))" by simp_all
      from `(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)`
	`(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l')`
      have [simp]:"ix = 0" "l' = lx" by simp_all
      from edge `fs = set_params ix (Suc lx) es`
      obtain n' es' rets ins outs c where "prog \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'"
	and "(p,ins,outs,c) \<in> set procs"	 and "targetnode a = (p,Entry)"
	by(auto elim!:PCFG.cases dest:fun_cong simp:valid_edge_def)
      from `valid_edge wfp a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` 
	`targetnode a' = (Main, Label (Suc l'))`
      have "sourcenode a' = (p,Exit)" by(fastsimp elim:PCFG.cases simp:valid_edge_def)
      from `prog \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'` 
      have "containsCall procs prog [] p es' rets" 
	by(rule Proc_CFG_Call_containsCall)
      with `(p,ins,outs,c) \<in> set procs`
      have "prog,procs \<turnstile> (p,Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (p,Exit)"
	by(fastsimp intro:Proc Proc_CFG_Entry_Exit)
      with `targetnode a = (p,Entry)` `sourcenode a' = (p,Exit)`
      show ?thesis by(fastsimp simp:valid_edge_def)
    next
      assume "\<exists>j. (THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l') \<and>
	targetnode a' = (fst (procs ! j), Label (Suc l')) \<and> j < length procs"
      then obtain j 
	where "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l')"
	and "targetnode a' = (fst (procs ! j), Label (Suc l'))"
	and "j < length procs" by blast
      from `(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)`
	`(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l')`
      have [simp]:"ix = Suc j" "lx = l'" by simp_all
      from edge `fs = set_params ix (Suc lx) es`
      obtain px ins outs c p' es' rets l'' ins' outs' c' ps esx retsx 
	where "j < length procs" and "procs ! j = (px,ins,outs,c)"
	and "c \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l''"
	and "(p,ins',outs',c') \<in> set procs" 
	and "containsCall procs prog ps px esx retsx"
	and "targetnode a = (p,Entry)"
	by(fastsimp elim!:PCFG.cases dest:fun_cong)
      from `valid_edge wfp a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` `procs ! j = (px,ins,outs,c)`
	`targetnode a' = (fst (procs ! j), Label (Suc l'))`
      have "sourcenode a' = (p,Exit)" by(fastsimp elim:PCFG.cases simp:valid_edge_def)
      from wf have "distinct_fst procs" by(simp add:well_formed_def)
      moreover
      from `c \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l''`
      have "containsCall procs c [] p es' rets" by(rule Proc_CFG_Call_containsCall)
      moreover
      from `j < length procs` `procs ! j = (px,ins,outs,c)`
      have "(px,ins,outs,c) \<in> set procs" by(fastsimp simp:in_set_conv_nth)
      ultimately have "containsCall procs prog (ps@[px]) p es' rets" 
	using `containsCall procs prog ps px esx retsx`
	by -(rule containsCall_in_proc)
      with `(p,ins',outs',c') \<in> set procs`
      have "prog,procs \<turnstile> (p,Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (p,Exit)"
	by(fastsimp intro:Proc Proc_CFG_Entry_Exit)
      with `targetnode a = (p,Entry)` `sourcenode a' = (p,Exit)`
      show ?thesis by(fastsimp simp:valid_edge_def)
    qed
  next
    fix a a'
    assume "valid_edge wfp a" and "a' \<in> get_return_edges wfp a"
    then obtain Q p fs l'
      where "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge wfp a'"
      and disj:"((THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l') \<and>
      targetnode a' = (Main, Label (Suc l'))) \<or>
      (\<exists>j. (THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j,l') \<and>
      targetnode a' = (fst (procs ! j), Label (Suc l')) \<and> j < length procs)"
      apply(cases "kind a") apply(auto simp:valid_edge_def get_return_edges_def)
      by(case_tac x)(fastsimp simp:valid_edge_def Let_def split:split_if_asm)+
    from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges wfp a`
    obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" 
      by(fastsimp dest!:only_return_edges_in_get_return_edges)
    from `valid_edge wfp a` `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have edge:"prog,procs \<turnstile> sourcenode a -Q\<hookrightarrow>\<^bsub>p\<^esub>fs\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from edge obtain ix lx es where "fs = set_params ix (Suc lx) es" 
      by(fastsimp dest:PCFG_CallEdge_set_params)
    with edge have "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)"
      by(fastsimp intro:PCFG_CallEdge_THE_set_params)
    from disj show "\<exists>a''. valid_edge wfp a'' \<and>
      sourcenode a'' = sourcenode a \<and> targetnode a'' = targetnode a' \<and> 
      kind a'' = (\<lambda>cf. False)\<^isub>\<surd>"
    proof
      assume "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l') \<and>
	targetnode a' = (Main, Label (Suc l'))"
      hence "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l')"
	and "targetnode a' = (Main, Label (Suc l'))" by simp_all
      from `(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)`
	`(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (0,l')`
      have [simp]:"ix = 0" "l' = lx" by simp_all
      from edge `fs = set_params ix (Suc lx) es`
      obtain n' es' rets ins outs c where "prog \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'"
	and "sourcenode a = (Main,Label lx)" and "distinct rets"
	by(auto elim!:PCFG.cases dest:fun_cong simp:valid_edge_def)
      from `prog \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'` have "n' = Label (Suc l')"
	by(fastsimp dest:Proc_CFG_Call_Labels)
      with `prog \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p n'` `distinct rets`
      have "prog,procs \<turnstile> (Main,Label l') -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> 
	(Main,Label (Suc l'))" by(fastsimp intro:MainCallReturn)
      with `targetnode a' = (Main, Label (Suc l'))` `sourcenode a = (Main,Label lx)`
      show ?thesis by(fastsimp simp:valid_edge_def)
    next
      assume "\<exists>j. (THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l') \<and>
	targetnode a' = (fst (procs ! j), Label (Suc l')) \<and> j < length procs"
      then obtain j 
	where "(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l')"
	and "targetnode a' = (fst (procs ! j), Label (Suc l'))"
	and "j < length procs" by blast
      from `(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (ix,lx)`
	`(THE (i, l). \<exists>es. fs = set_params i (Suc l) es) = (Suc j, l')`
      have [simp]:"ix = Suc j" "lx = l'" by simp_all
      from edge `fs = set_params ix (Suc lx) es`
      obtain px ins outs c p' es' rets l'' esx retsx ps
	where "j < length procs" and "procs ! j = (px,ins,outs,c)"
	and "c \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l''"
	and "containsCall procs prog ps px esx retsx"
	and "sourcenode a = (px,Label lx)" and "distinct rets"
	by(fastsimp elim!:PCFG.cases dest:fun_cong)
      from `j < length procs` `procs ! j = (px,ins,outs,c)`
	`targetnode a' = (fst (procs ! j), Label (Suc l'))`
      have "targetnode a' = (px, Label (Suc l'))" by simp
      from `c \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l''` have "l'' = Suc l'"
	by(fastsimp dest:Proc_CFG_Call_Labels)
      with `c \<turnstile> Label lx -CEdge (p,es',rets)\<rightarrow>\<^isub>p Label l''`
	`j < length procs` `procs ! j = (px,ins,outs,c)`[THEN sym]
	`containsCall procs prog ps px esx retsx` `distinct rets`
      have "prog,procs \<turnstile> (px,Label l') -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> 
	(px,Label (Suc l'))" by(auto intro!:ProcCallReturn simp:set_conv_nth)
      with `sourcenode a = (px,Label lx)` `targetnode a' = (px, Label (Suc l'))`
      show ?thesis by(fastsimp simp:valid_edge_def)
    qed
  next
    fix a Q p fs
    assume "valid_edge wfp a" and "kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q\<hookrightarrow>\<^bsub>p\<^esub>fs` 
    show "\<exists>!a'. valid_edge wfp a' \<and>
      sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainCall l p' es rets n' ins outs c)
      show ?thesis 
      proof(rule ex_ex1I)
	from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p n'` `distinct rets`
	have "prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,n')"
	  by(rule MainCallReturn)
	with `(Main, Label l) = sourcenode a`[THEN sym]
	show "\<exists>a'. valid_edge wfp a' \<and>
          sourcenode a' = sourcenode a \<and> intra_kind (kind a')"
	  by(fastsimp simp:valid_edge_def intra_kind_def) 
      next
	fix a' a'' 
	assume "valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
	  intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          sourcenode a'' = sourcenode a \<and> intra_kind (kind a'')"
	hence "valid_edge wfp a'" and "sourcenode a' = sourcenode a"
	  and "intra_kind (kind a')" and "valid_edge wfp a''"
	  and "sourcenode a'' = sourcenode a" and "intra_kind (kind a'')" by simp_all
	from `valid_edge wfp a'` `sourcenode a' = sourcenode a`
	  `intra_kind (kind a')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p n'`
	  `(Main, Label l) = sourcenode a` wf
	have "targetnode a' = (Main,Label (Suc l))"
	  by(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_source 
	    Proc_CFG_Call_Labels simp:intra_kind_def valid_edge_def)
	from `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
	  `intra_kind (kind a'')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p n'`
	  `(Main, Label l) = sourcenode a` wf
	have "targetnode a'' = (Main,Label (Suc l))"
	  by(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_source 
	    Proc_CFG_Call_Labels simp:intra_kind_def valid_edge_def)
	with `valid_edge wfp a'` `sourcenode a' = sourcenode a`
	  `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
	  `targetnode a' = (Main,Label (Suc l))` wf
	show "a' = a''" by(cases a',cases a'')
	(auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    next
      case (ProcCall i px ins outs c l p' es' rets' l' ins' outs' c' ps esx retsx)
      show ?thesis 
      proof(rule ex_ex1I)
	from `i < length procs` `procs ! i = (px, ins, outs, c)`[THEN sym]
	have "(px, ins, outs, c) \<in> set procs" by(fastsimp simp:set_conv_nth)
	with `containsCall procs prog ps px esx retsx`
	  `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'` `distinct rets'`
	have "prog,procs \<turnstile> (px,Label l) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (px,Label l')"
	  by -(rule ProcCallReturn)
	with `(px, Label l) = sourcenode a`[THEN sym]
	show "\<exists>a'. valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
	           intra_kind (kind a')"
	  by(fastsimp simp:valid_edge_def intra_kind_def)
      next
	fix a' a'' 
	assume "valid_edge wfp a' \<and> sourcenode a' = sourcenode a \<and> 
	  intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          sourcenode a'' = sourcenode a \<and> intra_kind (kind a'')"
	hence "valid_edge wfp a'" and "sourcenode a' = sourcenode a"
	  and "intra_kind (kind a')" and "valid_edge wfp a''"
	  and "sourcenode a'' = sourcenode a" and "intra_kind (kind a'')" by simp_all
	from `valid_edge wfp a'` `sourcenode a' = sourcenode a`
	  `intra_kind (kind a')` `i < length procs` `procs ! i = (px, ins, outs, c)`
	  `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
	  `(p', ins', outs', c') \<in> set procs` wf
	  `containsCall procs prog ps px esx retsx` `(px, Label l) = sourcenode a`
	have "targetnode a' = (px,Label (Suc l))"
	  apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
	  by(auto dest:Proc_CFG_Call_Intra_edge_not_same_source 
	    Proc_CFG_Call_nodes_eq Proc_CFG_Call_Labels simp:intra_kind_def)
	from `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
	  `intra_kind (kind a'')` `i < length procs`
	  `procs ! i = (px, ins, outs, c)`
	  `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
	  `(p', ins', outs', c') \<in> set procs` wf
	  `containsCall procs prog ps px esx retsx` `(px, Label l) = sourcenode a`
	have "targetnode a'' = (px,Label (Suc l))"
	  apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
	  by(auto dest:Proc_CFG_Call_Intra_edge_not_same_source 
	    Proc_CFG_Call_nodes_eq Proc_CFG_Call_Labels simp:intra_kind_def)
	with `valid_edge wfp a'` `sourcenode a' = sourcenode a`
	  `valid_edge wfp a''` `sourcenode a'' = sourcenode a`
	  `targetnode a' = (px,Label (Suc l))` wf
	show "a' = a''" by(cases a',cases a'')
	(auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    qed auto
  next
    fix a Q' p f'
    assume "valid_edge wfp a" and "kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
    hence "prog,procs \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"
      by(simp add:valid_edge_def)
    from this `kind a = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
    show "\<exists>!a'. valid_edge wfp a' \<and>
      targetnode a' = targetnode a \<and> intra_kind (kind a')"
    proof(induct n\<equiv>"sourcenode a" et\<equiv>"kind a" n'\<equiv>"targetnode a" rule:PCFG.induct)
      case (MainReturn l p' es rets l' ins outs c)
      show ?thesis 
      proof(rule ex_ex1I)
	from `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p Label l'` `distinct rets`
	have "prog,procs \<turnstile> (Main,Label l) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> 
	  (Main,Label l')" by(rule MainCallReturn)
	with `(Main, Label l') = targetnode a`[THEN sym]
	show "\<exists>a'. valid_edge wfp a' \<and>
          targetnode a' = targetnode a \<and> intra_kind (kind a')"
	  by(fastsimp simp:valid_edge_def intra_kind_def)
      next
	fix a' a''
	assume "valid_edge wfp a' \<and> targetnode a' = targetnode a \<and> 
	  intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          targetnode a'' = targetnode a \<and> intra_kind (kind a'')"
	hence "valid_edge wfp a'" and "targetnode a' = targetnode a"
	  and "intra_kind (kind a')" and "valid_edge wfp a''"
	  and "targetnode a'' = targetnode a" and "intra_kind (kind a'')" by simp_all
	from `valid_edge wfp a'` `targetnode a' = targetnode a`
	  `intra_kind (kind a')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p Label l'`
	  `(Main, Label l') = targetnode a` wf
	have "sourcenode a' = (Main,Label l)"
	  apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_target 
	              simp:valid_edge_def intra_kind_def)
	  by(fastsimp dest:Proc_CFG_Call_nodes_eq' Proc_CFG_Call_Labels)
	from `valid_edge wfp a''` `targetnode a'' = targetnode a`
	  `intra_kind (kind a'')` `prog \<turnstile> Label l -CEdge (p', es, rets)\<rightarrow>\<^isub>p Label l'`
	  `(Main, Label l') = targetnode a` wf
	have "sourcenode a'' = (Main,Label l)"
	  apply(auto elim!:PCFG.cases dest:Proc_CFG_Call_Intra_edge_not_same_target 
	              simp:valid_edge_def intra_kind_def)
	  by(fastsimp dest:Proc_CFG_Call_nodes_eq' Proc_CFG_Call_Labels)
	with `valid_edge wfp a'` `targetnode a' = targetnode a`
	  `valid_edge wfp a''` `targetnode a'' = targetnode a`
	  `sourcenode a' = (Main,Label l)` wf
	show "a' = a''" by(cases a',cases a'')
	(auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    next
      case (ProcReturn i px ins outs c l p' es' rets' l' ins' outs' c' ps esx retsx)
      show ?thesis 
      proof(rule ex_ex1I)
	from `i < length procs` `procs ! i = (px, ins, outs, c)`[THEN sym]
	have "(px, ins, outs, c) \<in> set procs" by(fastsimp simp:set_conv_nth)
	with `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
	  `distinct rets'` `containsCall procs prog ps px esx retsx`
	have "prog,procs \<turnstile> (px,Label l) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (px,Label l')"
	  by -(rule ProcCallReturn)
	with `(px, Label l') = targetnode a`[THEN sym]
	show "\<exists>a'. valid_edge wfp a' \<and>
          targetnode a' = targetnode a \<and> intra_kind (kind a')"
	  by(fastsimp simp:valid_edge_def intra_kind_def)
      next
	fix a' a''
	assume "valid_edge wfp a' \<and> targetnode a' = targetnode a \<and> 
	  intra_kind (kind a')" and "valid_edge wfp a'' \<and>
          targetnode a'' = targetnode a \<and> intra_kind (kind a'')"
	hence "valid_edge wfp a'" and "targetnode a' = targetnode a"
	  and "intra_kind (kind a')" and "valid_edge wfp a''"
	  and "targetnode a'' = targetnode a" and "intra_kind (kind a'')" by simp_all
	from `valid_edge wfp a'` `targetnode a' = targetnode a`
	  `intra_kind (kind a')` `i < length procs`
	  `procs ! i = (px, ins, outs, c)` `(p', ins', outs', c') \<in> set procs` wf
	  `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
	  `containsCall procs prog ps px esx retsx` `(px, Label l') = targetnode a`
	have "sourcenode a' = (px,Label l)"
	  apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
	  by(auto dest:Proc_CFG_Call_Intra_edge_not_same_target 
	    Proc_CFG_Call_nodes_eq' simp:intra_kind_def)
	from `valid_edge wfp a''` `targetnode a'' = targetnode a`
	  `intra_kind (kind a'')` `i < length procs`
	  `procs ! i = (px, ins, outs, c)` `(p', ins', outs', c') \<in> set procs` wf
	  `c \<turnstile> Label l -CEdge (p', es', rets')\<rightarrow>\<^isub>p Label l'`
	  `containsCall procs prog ps px esx retsx` `(px, Label l') = targetnode a`
	have "sourcenode a'' = (px,Label l)"
	  apply(auto simp:valid_edge_def) apply(erule PCFG.cases)
	  by(auto dest:Proc_CFG_Call_Intra_edge_not_same_target 
	    Proc_CFG_Call_nodes_eq' simp:intra_kind_def)
	with `valid_edge wfp a'` `targetnode a' = targetnode a`
	  `valid_edge wfp a''` `targetnode a'' = targetnode a`
	  `sourcenode a' = (px,Label l)` wf
	show "a' = a''" by(cases a',cases a'')
	(auto dest:Proc_CFG_edge_det simp:valid_edge_def)
      qed
    qed auto
  next
    fix a a' Q\<^isub>1 p fs\<^isub>1 Q\<^isub>2 fs\<^isub>2
    assume "valid_edge wfp a" and "valid_edge wfp a'"
      and "kind a = Q\<^isub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^isub>1" and "kind a' = Q\<^isub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^isub>2"
    thus "targetnode a = targetnode a'" by(auto elim!:PCFG.cases simp:valid_edge_def)
  next
    from wf show "distinct_fst (lift_procs wfp)"
      by(fastsimp simp:well_formed_def distinct_fst_def map_compose[symmetric] o_def)
  next
    fix p ins outs assume "(p, ins, outs) \<in> set (lift_procs wfp)"
    from `(p, ins, outs) \<in> set (lift_procs wfp)` wf
    show "distinct ins" by(fastsimp simp:well_formed_def wf_proc_def)
  next
    fix p ins outs assume "(p, ins, outs) \<in> set (lift_procs wfp)"
    from `(p, ins, outs) \<in> set (lift_procs wfp)` wf
    show "distinct outs" by(fastsimp simp:well_formed_def wf_proc_def)
  qed
qed



subsection {* Instatiation of the @{text CFGExit} locale *}


interpretation ProcCFGExit:
  CFGExit sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
proof -
  from Rep_wf_prog[of wfp]
  obtain prog procs where [simp]:"Rep_wf_prog wfp = (prog,procs)" 
    by(fastsimp simp:wf_prog_def)
  hence wf:"well_formed procs" by(fastsimp intro:wf_wf_prog)
  show "CFGExit sourcenode targetnode kind (valid_edge wfp) (Main, Entry)
    get_proc (get_return_edges wfp) (lift_procs wfp) Main (Main, Exit)"
  proof
    fix a assume "valid_edge wfp a" and "sourcenode a = (Main, Exit)"
    with wf show False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    show "get_proc (Main, Exit) = Main" by simp
  next
    fix a Q p f
    assume "valid_edge wfp a" and "kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f"
      and "targetnode a = (Main, Exit)"
    thus False by(auto elim:PCFG.cases simp:valid_edge_def)
  next
    have "prog,procs \<turnstile> (Main,Entry) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (Main,Exit)"
      by(fastsimp intro:Main Proc_CFG_Entry_Exit)
    thus "\<exists>a. valid_edge wfp a \<and>
      sourcenode a = (Main, Entry) \<and>
      targetnode a = (Main, Exit) \<and> kind a = (\<lambda>s. False)\<^isub>\<surd>"
      by(fastsimp simp:valid_edge_def)
  qed
qed


end