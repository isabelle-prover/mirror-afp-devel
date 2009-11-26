header {* \isaheader{The fundamental property of slicing} *}

theory FundamentalProperty imports WeakSimulation SemanticsCFG begin

context SDG begin

subsection {* Auxiliary lemmas for moves in the graph *}

lemma observable_set_stack_in_slice:
  "n\<^isub>c,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s') 
  \<Longrightarrow> \<forall>mx \<in> set (tl ms'). \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
proof(induct rule:observable_move.induct)
  case (observable_move_intra f a s s' ms n\<^isub>c ms') thus ?case by simp
next
  case (observable_move_call f a s s' Q r p fs a' ms n\<^isub>c ms')
  from `valid_edge a` `valid_edge a'` `a' \<in> get_return_edges a`
  have "call_of_return_node (targetnode a') (sourcenode a)"
    by(fastsimp simp:return_node_def call_of_return_node_def)
  with `hd ms = sourcenode a` `hd ms \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` 
    `ms' = targetnode a # targetnode a' # tl ms`
    `\<forall>mx\<in>set (tl ms). \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  show ?case by fastsimp
next
  case (observable_move_return f a s s' Q p f' ms n\<^isub>c ms')
  thus ?case by(cases "tl ms") auto
qed


lemma silent_move_preserves_stacks:
  assumes "n\<^isub>c,f \<turnstile> (m#ms,s) -a\<rightarrow>\<^isub>\<tau> (m'#ms',s')" and "valid_call_list cs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" and "valid_return_list rs m"
  and "length rs = length cs" and "ms = targetnodes rs"
  obtains cs' rs' where "valid_node m'" and "valid_call_list cs' m'"
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'" and "upd_cs cs [a] = cs'"
proof(atomize_elim)
  from assms show "\<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
    valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
    upd_cs cs [a] = cs'"
  proof(induct n\<^isub>c f msx\<equiv>"m#ms" s a msx'\<equiv>"m'#ms'" s' rule:silent_move.induct)
    case (silent_move_intra f a s s' msx n\<^isub>c msx')
    from `msx = m # ms` `hd msx = sourcenode a` have "m = sourcenode a" by simp
    from `msx' = m' # ms'` `msx' = targetnode a # tl msx` `msx = m # ms`
    have [simp]:"m' = targetnode a" "ms' = ms" by simp_all
    from `valid_edge a` have "valid_node m'" by simp
    moreover
    from `valid_edge a` `intra_kind (kind a)`
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    from `valid_call_list cs m` `m = sourcenode a`
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_call_list cs m'"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    moreover
    from `valid_return_list rs m` `m = sourcenode a` 
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_return_list rs m'"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="cs'" in allE) apply clarsimp
      by(case_tac cs') auto
    moreover
    from `intra_kind (kind a)` have "upd_cs cs [a] = cs"
      by(fastsimp simp:intra_kind_def)
    ultimately show ?case using `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
      `length rs = length cs` `ms = targetnodes rs`
      apply(rule_tac x="cs" in exI)
      apply(rule_tac x="rs" in exI) 
      by clarsimp
  next
    case (silent_move_call f a s s' Q r p fs a' msx n\<^isub>c msx')
    from `msx = m # ms` `msx' = m' # ms'` `hd msx = sourcenode a` 
      `msx' = targetnode a # targetnode a' # tl msx`
    have [simp]:"m = sourcenode a" "m' = targetnode a" 
      "ms = tl msx" "ms' = targetnode a' # tl msx"
      by simp_all
    from `valid_edge a` have "valid_node m'" by simp
    moreover
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
      by(rule get_proc_call)
    with `valid_call_list cs m` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m = sourcenode a`
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    moreover
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `a' \<in> get_return_edges a`
    have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
      by auto(case_tac i,auto)
    moreover
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
    obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" by(fastsimp dest!:call_return_edges)
    from `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have "get_proc (sourcenode a') = p"
      by(rule get_proc_return)
    from `valid_edge a` `a' \<in> get_return_edges a`
    have "get_proc (sourcenode a) = get_proc (targetnode a')" 
      by(rule get_proc_get_return_edge)
    with `valid_return_list rs m` `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
      `get_proc (sourcenode a') = p` `get_proc (targetnode a) = p` `m = sourcenode a`
    have "valid_return_list (a'#rs) (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:targetnodes_def)
    moreover
    from `length rs = length cs` have "length (a'#rs) = length (a#cs)" by simp
    moreover
    from `ms = targetnodes rs` have "targetnode a' # ms = targetnodes (a' # rs)"
      by(simp add:targetnodes_def)
    moreover
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs cs [a] = a#cs" by simp
    ultimately show ?case
      apply(rule_tac x="a#cs" in exI)
      apply(rule_tac x="a'#rs" in exI)
      by clarsimp
  next
    case (silent_move_return f a s s' Q p f' msx n\<^isub>c msx')
    from `msx = m # ms` `msx' = m' # ms'` `hd msx = sourcenode a`
      `hd (tl msx) = targetnode a` `msx' = tl msx`
    have [simp]:"m = sourcenode a" "m' = targetnode a" by simp_all
    from `msx = m # ms` `length msx = length s` `length s = Suc (length s')` `s' \<noteq> []`
      `hd (tl msx) = targetnode a` `msx' = m' # ms'` `msx' = tl msx`
    have "ms = targetnode a # ms'" 
      by(cases ms) auto
    with `ms = targetnodes rs`
    obtain r' rs' where "rs = r' # rs'" 
      and "targetnode a = targetnode r'" and "ms' = targetnodes rs'" 
      by(cases rs)(auto simp:targetnodes_def)
    moreover
    from `rs = r' # rs'` `length rs = length cs` obtain c' cs' where "cs = c' # cs'"
      and "length rs' = length cs'" by(cases cs) auto
    moreover
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
      `rs = r' # rs'` `cs = c' # cs'`
    have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      and "r' \<in> get_return_edges c'" by auto
    moreover
    from `valid_edge a` have "valid_node (targetnode a)" by simp
    moreover
    from `valid_call_list cs m` `cs = c' # cs'`
    obtain p' Q' r fs' where "valid_edge c'" and "kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'" 
      and "p' = get_proc m"
      apply(auto simp:valid_call_list_def)
      by(erule_tac x="[]" in allE) auto
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'`
    have "get_proc (sourcenode a) = p" by(rule get_proc_return)
    with `p' = get_proc m` have [simp]:"p' = p" by simp
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
    have "get_proc (targetnode c') = p" by(fastsimp intro:get_proc_call)
    from `valid_edge c'` `r' \<in> get_return_edges c'` have "valid_edge r'"
      by(rule get_return_edges_valid)
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `r' \<in> get_return_edges c'`
    obtain Q'' f'' where "kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''" by(fastsimp dest!:call_return_edges)
    with `valid_edge r'` have "get_proc (sourcenode r') = p" by(rule get_proc_return)
    from `valid_edge r'` `kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''` have "method_exit (sourcenode r')" 
      by(fastsimp simp:method_exit_def)
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` have "method_exit (sourcenode a)" 
      by(fastsimp simp:method_exit_def)
    with `method_exit (sourcenode r')` `get_proc (sourcenode r') = p` 
      `get_proc (sourcenode a) = p`
    have "sourcenode a = sourcenode r'" by(fastsimp intro:method_exit_unique)
    with `valid_edge a` `valid_edge r'` `targetnode a = targetnode r'`
    have "a = r'" by(fastsimp intro:edge_det)
    from `valid_edge c'` `r' \<in> get_return_edges c'` `targetnode a = targetnode r'`
    have "get_proc (sourcenode c') = get_proc (targetnode a)"
      by(fastsimp intro:get_proc_get_return_edge)
    from `valid_call_list cs m` `cs = c' # cs'`
      `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    moreover
    from `valid_return_list rs m` `rs = r' # rs'` `targetnode a = targetnode r'`
    have "valid_return_list rs' (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="r' # cs'" in allE)
      by(case_tac cs')(auto simp:targetnodes_def)
    moreover
    from `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` `cs = c' # cs'` have "upd_cs cs [a] = cs'" by simp
    ultimately show ?case
      apply(rule_tac x="cs'" in exI)
      apply(rule_tac x="rs'" in exI)
      by clarsimp
  qed
qed


lemma silent_moves_preserves_stacks:
  assumes "n\<^isub>c,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" 
  and "valid_node m" and "valid_call_list cs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" and "valid_return_list rs m"
  and "length rs = length cs" and "ms = targetnodes rs"
  obtains cs' rs' where "valid_node m'" and "valid_call_list cs' m'"
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'" and "upd_cs cs as = cs'"
proof(atomize_elim)
  from assms show "\<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
    valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
    upd_cs cs as = cs'"
  proof(induct n\<^isub>c f msx\<equiv>"m#ms" s as msx\<equiv>"m'#ms'" s' 
      arbitrary:m ms cs rs rule:silent_moves.induct)
    case (silent_moves_Nil msx s n\<^isub>c f)
    thus ?case
      apply(rule_tac x="cs" in exI)
      apply(rule_tac x="rs" in exI)
      by clarsimp
  next
    case (silent_moves_Cons n\<^isub>c f msx s a msx'' s'' as msx' sx')
    note IH = `\<And>m ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i);
      valid_return_list rs m; length rs = length cs; ms = targetnodes rs;
      msx'' = m # ms; msx' = m' # ms'\<rbrakk>
      \<Longrightarrow> \<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
      (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
      valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
      upd_cs cs as = cs'`
    from `n\<^isub>c,f \<turnstile> (msx,s) -a\<rightarrow>\<^isub>\<tau> (msx'',s'')` `msx = m # ms`
    obtain m'' ms'' where "msx'' = m''#ms''"
      by(cases msx'')(auto elim:silent_move.cases)
    with `n\<^isub>c,f \<turnstile> (msx,s) -a\<rightarrow>\<^isub>\<tau> (msx'',s'')` `msx = m # ms` `valid_call_list cs m`
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `valid_return_list rs m`
      `length rs = length cs` `ms = targetnodes rs`
    obtain cs'' rs'' where hyps:"valid_node m''" "valid_call_list cs'' m''"
      "\<forall>i < length rs''. rs''!i \<in> get_return_edges (cs''!i)"
      "valid_return_list rs'' m''" "length rs'' = length cs''" 
      "ms'' = targetnodes rs''" and "upd_cs cs [a] = cs''"
      by(auto elim!:silent_move_preserves_stacks)
    from IH[OF hyps] `msx'' = m'' # ms''` `msx' = m' # ms'`
    obtain cs' rs' where results:"valid_node m'" "valid_call_list cs' m'"
      "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      "valid_return_list rs' m'" "length rs' = length cs'" "ms' = targetnodes rs'"
      and "upd_cs cs'' as = cs'" by blast
    from `upd_cs cs [a] = cs''` `upd_cs cs'' as = cs'` 
    have "upd_cs cs ([a] @ as) = cs'" by(rule upd_cs_Append)
    with results show ?case
      apply(rule_tac x="cs'" in exI)
      apply(rule_tac x="rs'" in exI)
      by clarsimp
  qed
qed


lemma observable_move_preserves_stacks:
  assumes "n\<^isub>c,f \<turnstile> (m#ms,s) -a\<rightarrow> (m'#ms',s')" and "valid_call_list cs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" and "valid_return_list rs m"
  and "length rs = length cs" and "ms = targetnodes rs"
  obtains cs' rs' where "valid_node m'" and "valid_call_list cs' m'"
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'" and "upd_cs cs [a] = cs'"
proof(atomize_elim)
  from assms show "\<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
    valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
    upd_cs cs [a] = cs'"
  proof(induct n\<^isub>c f msx\<equiv>"m#ms" s a msx'\<equiv>"m'#ms'" s' rule:observable_move.induct)
    case (observable_move_intra f a s s' msx n\<^isub>c msx')
    from `msx = m # ms` `hd msx = sourcenode a` have "m = sourcenode a" by simp
    from `msx' = m' # ms'` `msx' = targetnode a # tl msx` `msx = m # ms`
    have [simp]:"m' = targetnode a" "ms' = ms" by simp_all
    from `valid_edge a` have "valid_node m'" by simp
    moreover
    from `valid_edge a` `intra_kind (kind a)`
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    from `valid_call_list cs m` `m = sourcenode a`
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_call_list cs m'"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    moreover
    from `valid_return_list rs m` `m = sourcenode a` 
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_return_list rs m'"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="cs'" in allE) apply clarsimp
      by(case_tac cs') auto
    moreover
    from `intra_kind (kind a)` have "upd_cs cs [a] = cs"
      by(fastsimp simp:intra_kind_def)
    ultimately show ?case using `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
      `length rs = length cs` `ms = targetnodes rs`
      apply(rule_tac x="cs" in exI)
      apply(rule_tac x="rs" in exI) 
      by clarsimp
  next
    case (observable_move_call f a s s' Q r p fs a' msx n\<^isub>c msx')
    from `msx = m # ms` `msx' = m' # ms'` `hd msx = sourcenode a` 
      `msx' = targetnode a # targetnode a' # tl msx`
    have [simp]:"m = sourcenode a" "m' = targetnode a" 
      "ms = tl msx" "ms' = targetnode a' # tl msx"
      by simp_all
    from `valid_edge a` have "valid_node m'" by simp
    moreover
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
      by(rule get_proc_call)
    with `valid_call_list cs m` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m = sourcenode a`
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    moreover
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `a' \<in> get_return_edges a`
    have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
      by auto(case_tac i,auto)
    moreover
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
    obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" by(fastsimp dest!:call_return_edges)
    from `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have "get_proc (sourcenode a') = p"
      by(rule get_proc_return)
    from `valid_edge a` `a' \<in> get_return_edges a`
    have "get_proc (sourcenode a) = get_proc (targetnode a')" 
      by(rule get_proc_get_return_edge)
    with `valid_return_list rs m` `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
      `get_proc (sourcenode a') = p` `get_proc (targetnode a) = p` `m = sourcenode a`
    have "valid_return_list (a'#rs) (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:targetnodes_def)
    moreover
    from `length rs = length cs` have "length (a'#rs) = length (a#cs)" by simp
    moreover
    from `ms = targetnodes rs` have "targetnode a' # ms = targetnodes (a' # rs)"
      by(simp add:targetnodes_def)
    moreover
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "upd_cs cs [a] = a#cs" by simp
    ultimately show ?case
      apply(rule_tac x="a#cs" in exI)
      apply(rule_tac x="a'#rs" in exI)
      by clarsimp
  next
    case (observable_move_return f a s s' Q p f' msx n\<^isub>c msx')
    from `msx = m # ms` `msx' = m' # ms'` `hd msx = sourcenode a`
      `hd (tl msx) = targetnode a` `msx' = tl msx`
    have [simp]:"m = sourcenode a" "m' = targetnode a" by simp_all
    from `msx = m # ms` `length msx = length s` `length s = Suc (length s')` `s' \<noteq> []`
      `hd (tl msx) = targetnode a` `msx' = m' # ms'` `msx' = tl msx`
    have "ms = targetnode a # ms'" 
      by(cases ms) auto
    with `ms = targetnodes rs`
    obtain r' rs' where "rs = r' # rs'" 
      and "targetnode a = targetnode r'" and "ms' = targetnodes rs'" 
      by(cases rs)(auto simp:targetnodes_def)
    moreover
    from `rs = r' # rs'` `length rs = length cs` obtain c' cs' where "cs = c' # cs'"
      and "length rs' = length cs'" by(cases cs) auto
    moreover
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
      `rs = r' # rs'` `cs = c' # cs'`
    have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      and "r' \<in> get_return_edges c'" by auto
    moreover
    from `valid_edge a` have "valid_node (targetnode a)" by simp
    moreover
    from `valid_call_list cs m` `cs = c' # cs'`
    obtain p' Q' r fs' where "valid_edge c'" and "kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'" 
      and "p' = get_proc m"
      apply(auto simp:valid_call_list_def)
      by(erule_tac x="[]" in allE) auto
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'`
    have "get_proc (sourcenode a) = p" by(rule get_proc_return)
    with `p' = get_proc m` have [simp]:"p' = p" by simp
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
    have "get_proc (targetnode c') = p" by(fastsimp intro:get_proc_call)
    from `valid_edge c'` `r' \<in> get_return_edges c'` have "valid_edge r'"
      by(rule get_return_edges_valid)
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `r' \<in> get_return_edges c'`
    obtain Q'' f'' where "kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''" by(fastsimp dest!:call_return_edges)
    with `valid_edge r'` have "get_proc (sourcenode r') = p" by(rule get_proc_return)
    from `valid_edge r'` `kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''` have "method_exit (sourcenode r')" 
      by(fastsimp simp:method_exit_def)
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` have "method_exit (sourcenode a)" 
      by(fastsimp simp:method_exit_def)
    with `method_exit (sourcenode r')` `get_proc (sourcenode r') = p` 
      `get_proc (sourcenode a) = p`
    have "sourcenode a = sourcenode r'" by(fastsimp intro:method_exit_unique)
    with `valid_edge a` `valid_edge r'` `targetnode a = targetnode r'`
    have "a = r'" by(fastsimp intro:edge_det)
    from `valid_edge c'` `r' \<in> get_return_edges c'` `targetnode a = targetnode r'`
    have "get_proc (sourcenode c') = get_proc (targetnode a)"
      by(fastsimp intro:get_proc_get_return_edge)
    from `valid_call_list cs m` `cs = c' # cs'`
      `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    moreover
    from `valid_return_list rs m` `rs = r' # rs'` `targetnode a = targetnode r'`
    have "valid_return_list rs' (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="r' # cs'" in allE)
      by(case_tac cs')(auto simp:targetnodes_def)
    moreover
    from `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` `cs = c' # cs'` have "upd_cs cs [a] = cs'" by simp
    ultimately show ?case
      apply(rule_tac x="cs'" in exI)
      apply(rule_tac x="rs'" in exI)
      by clarsimp
  qed
qed


lemma observable_moves_preserves_stack:
  assumes "n\<^isub>c,f \<turnstile> (m#ms,s) =as\<Rightarrow> (m'#ms',s')" 
  and "valid_node m" and "valid_call_list cs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" and "valid_return_list rs m"
  and "length rs = length cs" and "ms = targetnodes rs"
  obtains cs' rs' where "valid_node m'" and "valid_call_list cs' m'"
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'" and "upd_cs cs as = cs'"
proof(atomize_elim)
  from `n\<^isub>c,f \<turnstile> (m#ms,s) =as\<Rightarrow> (m'#ms',s')` obtain msx s'' as' a'
    where "as = as'@[a']" and "n\<^isub>c,f \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (msx,s'')"
    and "n\<^isub>c,f \<turnstile> (msx,s'') -a'\<rightarrow> (m'#ms',s')"
    by(fastsimp elim:observable_moves.cases)
  from `n\<^isub>c,f \<turnstile> (msx,s'') -a'\<rightarrow> (m'#ms',s')` obtain m'' ms''
    where [simp]:"msx = m''#ms''" by(cases msx)(auto elim:observable_move.cases)
  from `n\<^isub>c,f \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (msx,s'')` `valid_node m` `valid_call_list cs m`
    `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `valid_return_list rs m`
    `length rs = length cs` `ms = targetnodes rs`
  obtain cs'' rs'' where "valid_node m''" and "valid_call_list cs'' m''"
    and "\<forall>i < length rs''. rs''!i \<in> get_return_edges (cs''!i)"
    and "valid_return_list rs'' m''" and "length rs'' = length cs''" 
    and "ms'' = targetnodes rs''" and "upd_cs cs as' = cs''"
    by(auto elim!:silent_moves_preserves_stacks)
  with `n\<^isub>c,f \<turnstile> (msx,s'') -a'\<rightarrow> (m'#ms',s')`
  obtain cs' rs' where results:"valid_node m'" "valid_call_list cs' m'"
    "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
    "valid_return_list rs' m'" "length rs' = length cs'" "ms' = targetnodes rs'"
    and "upd_cs cs'' [a'] = cs'"
    by(auto elim!:observable_move_preserves_stacks)
  from `upd_cs cs as' = cs''` `upd_cs cs'' [a'] = cs'`
  have "upd_cs cs (as'@[a']) = cs'" by(rule upd_cs_Append)
  with `as = as'@[a']` results
  show "\<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
    valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
    upd_cs cs as = cs'"
    apply(rule_tac x="cs'" in exI)
    apply(rule_tac x="rs'" in exI)
    by clarsimp
qed


lemma silent_moves_slpa_path:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (m#ms''@ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s'); valid_node m; valid_call_list cs m;
  \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); valid_return_list rs m; 
  length rs = length cs; ms'' = targetnodes rs;
  \<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
  ms'' \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>);
  \<forall>mx \<in> set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = [] \<and> m -as\<rightarrow>* m' \<and> ms = ms'"
proof(induct n\<^isub>c f msx\<equiv>"m#ms''@ms" s as msx'\<equiv>"m'#ms'" s' arbitrary:m ms'' ms cs rs
    rule:silent_moves.induct)
  case (silent_moves_Nil msx sx n\<^isub>c f) thus ?case
    apply(cases ms'' rule:rev_cases) apply(auto intro:empty_path simp:targetnodes_def)
    by(cases rs rule:rev_cases,auto)+
next
  case (silent_moves_Cons n\<^isub>c f msx sx a msx' sx' as msx'' sx'')
  thus ?case
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' msx n\<^isub>c msx')
    note IH = `\<And>m ms'' ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); valid_return_list rs m;
      length rs = length cs; ms'' = targetnodes rs;
      \<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      ms'' \<noteq> [] \<longrightarrow>
        (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>);
      \<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      msx' = m # ms'' @ ms; msx'' = m' # ms'\<rbrakk>
      \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = [] \<and> m -as\<rightarrow>* m' \<and> ms = ms'`
    note callstack = `\<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    note callstack'' = `ms'' \<noteq> [] \<longrightarrow>
      (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)`
    note callstack' = `\<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    from `valid_edge a` have "valid_node (targetnode a)" by simp
    from `valid_edge a` `intra_kind (kind a)`
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    from `msx = m # ms'' @ ms` `hd msx = sourcenode a` have "m = sourcenode a" 
      by simp
    from `valid_call_list cs m` `m = sourcenode a`
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_call_list cs (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    from `valid_return_list rs m` `m = sourcenode a` 
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_return_list rs (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="cs'" in allE) apply clarsimp
      by(case_tac cs') auto
    from `msx = m # ms'' @ ms` `msx' = targetnode a # tl msx`
    have "msx' = targetnode a # ms'' @ ms" by simp
    from IH[OF `valid_node (targetnode a)` `valid_call_list cs (targetnode a)`
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
      `valid_return_list rs (targetnode a)` `length rs = length cs`
      `ms'' = targetnodes rs` callstack callstack'' callstack' this 
      `msx'' = m' # ms'`]
    have "same_level_path_aux cs as" and "upd_cs cs as = []"
      and "targetnode a -as\<rightarrow>* m'" and "ms = ms'" by simp_all
    from `intra_kind (kind a)` `same_level_path_aux cs as`
    have "same_level_path_aux cs (a # as)" by(fastsimp simp:intra_kind_def)
    moreover
    from `intra_kind (kind a)` `upd_cs cs as = []`
    have "upd_cs cs (a # as) = []" by(fastsimp simp:intra_kind_def)
    moreover
    from `valid_edge a` `m = sourcenode a` `targetnode a -as\<rightarrow>* m'`
    have "m -a # as\<rightarrow>* m'" by(fastsimp intro:Cons_path)
    ultimately show ?case using `ms = ms'` by simp
  next
    case (silent_move_call f a s s' Q r p fs a' msx n\<^isub>c msx')
    note IH = `\<And>m ms'' ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); valid_return_list rs m;
      length rs = length cs; ms'' = targetnodes rs;
      \<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      ms'' \<noteq> [] \<longrightarrow>
        (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>);
      \<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      msx' = m # ms'' @ ms; msx'' = m' # ms'\<rbrakk>
      \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = [] \<and> m -as\<rightarrow>* m' \<and> ms = ms'`
    note callstack = `\<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    note callstack'' = `ms'' \<noteq> [] \<longrightarrow>
      (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)`
    note callstack' = `\<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    from `valid_edge a` have "valid_node (targetnode a)" by simp
    from `msx = m # ms'' @ ms` `hd msx = sourcenode a` have "m = sourcenode a" 
      by simp
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
      by(rule get_proc_call)
    with `valid_call_list cs m` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m = sourcenode a`
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `a' \<in> get_return_edges a`
    have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
      by auto(case_tac i,auto)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
    obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" by(fastsimp dest!:call_return_edges)
    from `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have "get_proc (sourcenode a') = p"
      by(rule get_proc_return)
    from `valid_edge a` `a' \<in> get_return_edges a`
    have "get_proc (sourcenode a) = get_proc (targetnode a')" 
      by(rule get_proc_get_return_edge)
    with `valid_return_list rs m` `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
      `get_proc (sourcenode a') = p` `get_proc (targetnode a) = p` `m = sourcenode a`
    have "valid_return_list (a'#rs) (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:targetnodes_def)
    from `length rs = length cs` have "length (a'#rs) = length (a # cs)" by simp
    from `ms'' = targetnodes rs`
    have "targetnode a' # ms'' = targetnodes (a'#rs)" by(simp add:targetnodes_def)
    from `msx' = targetnode a # targetnode a' # tl msx` `msx = m # ms'' @ ms`
    have "msx' = targetnode a # targetnode a' # ms'' @ ms" by simp
    have "\<exists>mx'. call_of_return_node (last (targetnode a' # ms'')) mx' \<and>
      mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    proof(cases "ms'' = []")
      case True
      with `msx = m # ms'' @ ms` `(\<exists>m\<in>set (tl msx).
	\<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<or>
	hd msx \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` callstack
      have "sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" by fastsimp
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
	by(rule get_return_edges_valid)
      with `valid_edge a` `a' \<in> get_return_edges a`
      have "call_of_return_node (targetnode a') (sourcenode a)"
	by(fastsimp simp:call_of_return_node_def return_node_def)
      with `sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` True show ?thesis by fastsimp
    next
      case False
      with callstack'' show ?thesis by fastsimp
    qed
    hence "targetnode a' # ms'' \<noteq> [] \<longrightarrow>
      (\<exists>mx'. call_of_return_node (last (targetnode a' # ms'')) mx' \<and>
      mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)" by simp
    from IH[OF `valid_node (targetnode a)` `valid_call_list (a # cs) (targetnode a)`
      `\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)`
      `valid_return_list (a'#rs) (targetnode a)` `length (a'#rs) = length (a # cs)`
      `targetnode a' # ms'' = targetnodes (a'#rs)` callstack this callstack'
      _ `msx'' = m' # ms'`] `msx' = targetnode a # targetnode a' # ms'' @ ms`
    have "same_level_path_aux (a # cs) as" and "upd_cs (a # cs) as = []"
      and "targetnode a -as\<rightarrow>* m'" and "ms = ms'" by simp_all
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `same_level_path_aux (a # cs) as`
    have "same_level_path_aux cs (a # as)" by simp
    moreover
    from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs (a # cs) as = []` have "upd_cs cs (a # as) = []"
      by simp
    moreover
    from `valid_edge a` `m = sourcenode a` `targetnode a -as\<rightarrow>* m'`
    have "m -a # as\<rightarrow>* m'" by(fastsimp intro:Cons_path)
    ultimately show ?case using `ms = ms'` by simp
  next
    case (silent_move_return f a s s' Q p f' msx n\<^isub>c msx')
    note IH = `\<And>m ms'' ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); valid_return_list rs m;
      length rs = length cs; ms'' = targetnodes rs;
      \<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      ms'' \<noteq> [] \<longrightarrow>
        (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>);
      \<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      msx' = m # ms'' @ ms; msx'' = m' # ms'\<rbrakk>
      \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = [] \<and> m -as\<rightarrow>* m' \<and> ms = ms'`
    note callstack = `\<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    note callstack'' = `ms'' \<noteq> [] \<longrightarrow>
      (\<exists>mx'. call_of_return_node (last ms'') mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)`
    note callstack' = `\<forall>mx\<in>set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    have "ms'' \<noteq> []"
    proof
      assume "ms'' = []"
      with `msx = m # ms'' @ ms` callstack
	`\<exists>m\<in>set (tl msx). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
      show False by fastsimp
    qed
    with `msx = m # ms'' @ ms` `hd (tl msx) = targetnode a`
    obtain xs where "ms'' = targetnode a # xs" by(cases ms'') auto
    with `ms'' = targetnodes rs` obtain r' rs' where "rs = r' # rs'" 
      and "targetnode a = targetnode r'" and "xs = targetnodes rs'" 
      by(cases rs)(auto simp:targetnodes_def)
    from `rs = r' # rs'` `length rs = length cs` obtain c' cs' where "cs = c' # cs'"
      and "length rs' = length cs'" by(cases cs) auto
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
      `rs = r' # rs'` `cs = c' # cs'`
    have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      and "r' \<in> get_return_edges c'" by auto
    from `valid_edge a` have "valid_node (targetnode a)" by simp
    from `msx = m # ms'' @ ms` `hd msx = sourcenode a` have "m = sourcenode a" 
      by simp
    from `valid_call_list cs m` `cs = c' # cs'`
    obtain p' Q' r fs' where "valid_edge c'" and "kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'" 
      and "p' = get_proc m"
      apply(auto simp:valid_call_list_def)
      by(erule_tac x="[]" in allE) auto
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'`
    have "get_proc (sourcenode a) = p" by(rule get_proc_return)
    with `m = sourcenode a` `p' = get_proc m` have [simp]:"p' = p" by simp
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'`
    have "get_proc (targetnode c') = p" by(fastsimp intro:get_proc_call)
    from `valid_edge c'` `r' \<in> get_return_edges c'` have "valid_edge r'"
      by(rule get_return_edges_valid)
    from `valid_edge c'` `kind c' = Q':r\<hookrightarrow>\<^bsub>p'\<^esub>fs'` `r' \<in> get_return_edges c'`
    obtain Q'' f'' where "kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''" by(fastsimp dest!:call_return_edges)
    with `valid_edge r'` have "get_proc (sourcenode r') = p" by(rule get_proc_return)
    from `valid_edge r'` `kind r' = Q''\<^bsub>p\<^esub>\<hookleftarrow>f''` have "method_exit (sourcenode r')" 
      by(fastsimp simp:method_exit_def)
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` have "method_exit (sourcenode a)" 
      by(fastsimp simp:method_exit_def)
    with `method_exit (sourcenode r')` `get_proc (sourcenode r') = p` 
      `get_proc (sourcenode a) = p`
    have "sourcenode a = sourcenode r'" by(fastsimp intro:method_exit_unique)
    with `valid_edge a` `valid_edge r'` `targetnode a = targetnode r'`
    have "a = r'" by(fastsimp intro:edge_det)
    from `valid_edge c'` `r' \<in> get_return_edges c'` `targetnode a = targetnode r'`
    have "get_proc (sourcenode c') = get_proc (targetnode a)"
      by(fastsimp intro:get_proc_get_return_edge)
    from `valid_call_list cs m` `cs = c' # cs'`
      `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    from `valid_return_list rs m` `rs = r' # rs'` `targetnode a = targetnode r'`
    have "valid_return_list rs' (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="r' # cs'" in allE)
      by(case_tac cs')(auto simp:targetnodes_def)
    from `msx' = tl msx` `msx = m # ms'' @ ms` `ms'' = targetnode a # xs`
    have "msx' = targetnode a # xs @ ms" by simp
    from callstack'' `ms'' = targetnode a # xs`
    have "xs \<noteq> [] \<longrightarrow>
      (\<exists>mx'. call_of_return_node (last xs) mx' \<and> mx' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)"
      by fastsimp
    from IH[OF `valid_node (targetnode a)` `valid_call_list cs' (targetnode a)`
      `\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)` 
      `valid_return_list rs' (targetnode a)` `length rs' = length cs'`
      `xs = targetnodes rs'` callstack this callstack' `msx' = targetnode a # xs @ ms`
      `msx'' = m' # ms'`]
    have "same_level_path_aux cs' as" and "upd_cs cs' as = []"
      and "targetnode a -as\<rightarrow>* m'" and "ms = ms'" by simp_all
    from `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` `same_level_path_aux cs' as` `cs = c' # cs'`
      `r' \<in> get_return_edges c'` `a = r'`
    have "same_level_path_aux cs (a # as)" by simp
    moreover
    from `upd_cs cs' as = []` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` `cs = c' # cs'`
    have "upd_cs cs (a # as) = []" by simp
    moreover
    from `valid_edge a` `m = sourcenode a` `targetnode a -as\<rightarrow>* m'`
    have "m -a # as\<rightarrow>* m'" by(fastsimp intro:Cons_path)
    ultimately show ?case using `ms = ms'` by simp
  qed
qed


lemma silent_moves_slp:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s'); valid_node m; valid_call_list cs m;
  \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); valid_return_list rs m; 
  length rs = length cs; ms'' = targetnodes rs;
  \<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
  \<forall>mx \<in> set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> m -as\<rightarrow>\<^bsub>sl\<^esub>* m' \<and> ms = ms'"
  by(fastsimp dest!:silent_moves_slpa_path
                   [of _ _ _ "[]" _ _ _ _ _ _ "[]" "[]",simplified] 
              simp:targetnodes_def valid_call_list_def valid_return_list_def 
		   same_level_path_def slp_def)


lemma slpa_silent_moves_callstacks_eq:
  "\<lbrakk>same_level_path_aux cs as; n\<^isub>c,f \<turnstile> (m#msx@ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s');
  length ms = length ms'; valid_call_list cs m; 
  \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); valid_return_list rs m; 
  length rs = length cs; msx = targetnodes rs\<rbrakk>
  \<Longrightarrow> ms = ms'"
proof(induct arbitrary:m msx s rs rule:slpa_induct)
  case (slpa_empty cs)
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =[]\<Rightarrow>\<^isub>\<tau> (m' # ms',s')`
  have "msx@ms = ms'" by(fastsimp elim:silent_moves.cases)
  with `length ms = length ms'` show ?case by fastsimp
next
  case (slpa_intra cs a as)
  note IH = `\<And>m msx s rs. \<lbrakk>n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s');
    length ms = length ms'; valid_call_list cs m;
    \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i);
    valid_return_list rs m; length rs = length cs; msx = targetnodes rs\<rbrakk>
    \<Longrightarrow> ms = ms'`
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =a # as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')` obtain ms'' s''
  where "n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')"
    and "n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
    by(auto elim:silent_moves.cases)
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')` `intra_kind (kind a)`
  have "valid_edge a" and [simp]:"m = sourcenode a" "ms'' = targetnode a # msx @ ms"
    by(fastsimp elim:silent_move.cases simp:intra_kind_def)+
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  from `valid_call_list cs m` `m = sourcenode a`
    `get_proc (sourcenode a) = get_proc (targetnode a)`
  have "valid_call_list cs (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
  from `valid_return_list rs m` `m = sourcenode a` 
    `get_proc (sourcenode a) = get_proc (targetnode a)`
  have "valid_return_list rs (targetnode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs') auto
  from `n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')`
  have "n\<^isub>c,f \<turnstile> (targetnode a # msx @ ms,s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')" by simp
  from IH[OF this `length ms = length ms'` `valid_call_list cs (targetnode a)`
    `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` 
    `valid_return_list rs (targetnode a)` `length rs = length cs`
    `msx = targetnodes rs`] show ?case .
next
  case (slpa_Call cs a as Q r p fs)
  note IH = `\<And>m msx s rs. \<lbrakk>n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s');
    length ms = length ms'; valid_call_list (a # cs) m;
    \<forall>i<length rs. rs ! i \<in> get_return_edges ((a # cs) ! i);
    valid_return_list rs m; length rs = length (a # cs);
    msx = targetnodes rs\<rbrakk>
    \<Longrightarrow> ms = ms'`
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =a # as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')` obtain ms'' s''
    where "n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')"
    and "n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
    by(auto elim:silent_moves.cases)
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  obtain a' where "valid_edge a" and [simp]:"m = sourcenode a"
    and [simp]:"ms'' = targetnode a # targetnode a' # msx @ ms"
    and "a' \<in> get_return_edges a"
    by(auto elim:silent_move.cases simp:intra_kind_def)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with `valid_call_list cs m` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m = sourcenode a`
  have "valid_call_list (a # cs) (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE)
    by(case_tac list)(auto simp:sourcenodes_def)
  from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `a' \<in> get_return_edges a`
  have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
    by auto(case_tac i,auto)
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
    by(rule get_return_edges_valid)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
  obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'" by(fastsimp dest!:call_return_edges)
  from `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have "get_proc (sourcenode a') = p"
    by(rule get_proc_return)
  from `valid_edge a` `a' \<in> get_return_edges a`
  have "get_proc (sourcenode a) = get_proc (targetnode a')" 
    by(rule get_proc_get_return_edge)
  with `valid_return_list rs m` `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
    `get_proc (sourcenode a') = p` `get_proc (targetnode a) = p` `m = sourcenode a`
  have "valid_return_list (a'#rs) (targetnode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE)
    by(case_tac list)(auto simp:targetnodes_def)
  from `length rs = length cs` have "length (a'#rs) = length (a#cs)" by simp
  from `msx = targetnodes rs` have "targetnode a' # msx = targetnodes (a' # rs)"
    by(simp add:targetnodes_def)
  from `n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')`
  have "n\<^isub>c,f \<turnstile> (targetnode a # (targetnode a' # msx) @ ms,s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
    by simp
  from IH[OF this `length ms = length ms'` `valid_call_list (a # cs) (targetnode a)`
    `\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)`
    `valid_return_list (a'#rs) (targetnode a)` `length (a'#rs) = length (a#cs)`
    `targetnode a' # msx = targetnodes (a' # rs)`] show ?case .
next
  case (slpa_Return cs a as Q p f' c' cs')
  note IH = `\<And>m msx s rs. \<lbrakk>n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s');
    length ms = length ms'; valid_call_list cs' m;
    \<forall>i<length rs. rs ! i \<in> get_return_edges (cs' ! i); valid_return_list rs m; 
    length rs = length cs'; msx = targetnodes rs\<rbrakk>
    \<Longrightarrow> ms = ms'`
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) =a # as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')` obtain ms'' s''
    where "n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')"
    and "n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
    by(auto elim:silent_moves.cases)
  from `n\<^isub>c,f \<turnstile> (m # msx @ ms,s) -a\<rightarrow>\<^isub>\<tau> (ms'',s'')` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'`
  have "valid_edge a" and "m = sourcenode a" and "hd (msx @ ms) = targetnode a"
    and "ms'' = msx @ ms" and "s'' \<noteq> []" and "length s = Suc(length s'')"
    and "length (m # msx @ ms) = length s"
    by(auto elim:silent_move.cases simp:intra_kind_def)
  from `msx = targetnodes rs` `length rs = length cs` `cs = c' # cs'`
  obtain mx' msx' where "msx = mx'#msx'"
    by(cases msx)(fastsimp simp:targetnodes_def)+
  with `hd (msx @ ms) = targetnode a` have "mx' = targetnode a" by simp
  from `valid_call_list cs m` `cs = c' # cs'` have "valid_edge c'"
    by(fastsimp simp:valid_call_list_def)
  from `valid_edge c'` `a \<in> get_return_edges c'`
  have "get_proc (sourcenode c') = get_proc (targetnode a)"
    by(rule get_proc_get_return_edge)
  from `valid_call_list cs m` `cs = c' # cs'`
    `get_proc (sourcenode c') = get_proc (targetnode a)`
  have "valid_call_list cs' (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="c' # cs'" in allE)
    by(case_tac cs')(auto simp:sourcenodes_def)
  from `length rs = length cs` `cs = c' # cs'` obtain r' rs' 
    where [simp]:"rs = r'#rs'" and "length rs' = length cs'" by(cases rs) auto
  from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `cs = c' # cs'`
  have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
    and "r' \<in> get_return_edges c'" by auto
  with `valid_edge c'` `a \<in> get_return_edges c'` have [simp]:"a = r'" 
    by -(rule get_return_edges_unique)
  with `valid_return_list rs m` 
  have "valid_return_list rs' (targetnode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="r' # cs'" in allE)
    by(case_tac cs')(auto simp:targetnodes_def)
  from `msx = targetnodes rs` `msx = mx'#msx'` `rs = r'#rs'`
  have "msx' = targetnodes rs'" by(simp add:targetnodes_def)
  from `n\<^isub>c,f \<turnstile> (ms'',s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')` `msx = mx'#msx'`
    `ms'' = msx @ ms` `mx' = targetnode a`
  have "n\<^isub>c,f \<turnstile> (targetnode a # msx' @ ms,s'') =as\<Rightarrow>\<^isub>\<tau> (m' # ms',s')" by simp
  from IH[OF this `length ms = length ms'` `valid_call_list cs' (targetnode a)`
    `\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)`
    `valid_return_list rs' (targetnode a)` `length rs' = length cs'`
    `msx' = targetnodes rs'`] show ?case .
qed


lemma silent_moves_same_level_path:
  assumes "n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" and "m -as\<rightarrow>\<^bsub>sl\<^esub>* m'" shows "ms = ms'"
proof -
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` obtain cf cfs where "s = cf#cfs"
    by(cases s)(auto dest:silent_moves_equal_length)
  with `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` 
  have "transfers (kinds as) (cf#cfs) = s'"
    by(fastsimp intro:silent_moves_preds_transfers simp:kinds_def)
  with `m -as\<rightarrow>\<^bsub>sl\<^esub>* m'` obtain cf' where "s' = cf'#cfs"
    by -(drule slp_callstack_length_equal,auto)
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
  have "length (m#ms) = length s" and "length (m'#ms') = length s'" 
    by(rule silent_moves_equal_length)+
  with `s = cf#cfs` `s' = cf'#cfs` have "length ms = length ms'" by simp
  from `m -as\<rightarrow>\<^bsub>sl\<^esub>* m'` have "same_level_path_aux [] as"
    by(simp add:slp_def same_level_path_def)
  with `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `length ms = length ms'` 
  show ?thesis by(auto elim!:slpa_silent_moves_callstacks_eq 
    simp:targetnodes_def valid_call_list_def valid_return_list_def)
qed


lemma silent_moves_call_edge:
  assumes "n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" and "valid_node m"
  and callstack:"\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  and rest:"\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)"
  "ms = targetnodes rs" "valid_return_list rs m" "length rs = length cs"
  obtains as' a as'' where "as = as'@a#as''" and "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "call_of_return_node (hd ms') (sourcenode a)"
  and "targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'"
  | "ms' = ms"
proof(atomize_elim)
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
  show "(\<exists>as' a as''. as = as' @ a # as'' \<and> (\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
    call_of_return_node (hd ms') (sourcenode a) \<and> targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m') \<or>
    ms' = ms"
  proof(induct as arbitrary:m' ms' s' rule:length_induct)
    fix as m' ms' s'
    assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
      (\<forall>mx msx sx. n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (mx#msx,sx) \<longrightarrow> 
      (\<exists>asx a asx'. as' = asx @ a # asx' \<and> (\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
      call_of_return_node (hd msx) (sourcenode a) \<and> targetnode a -asx'\<rightarrow>\<^bsub>sl\<^esub>* mx) \<or>
      msx = ms)"
      and "n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
    show "(\<exists>as' a as''. as = as' @ a # as'' \<and> (\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
      call_of_return_node (hd ms') (sourcenode a) \<and> targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m') \<or>
      ms' = ms"
    proof(cases as rule:rev_cases)
      case Nil
      with `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` have "ms = ms'"
	by(fastsimp elim:silent_moves.cases)
      thus ?thesis by simp
    next
      case (snoc as' a')
      with `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
      obtain ms'' s'' where "n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (ms'',s'')"
	and "n\<^isub>c,kind \<turnstile> (ms'',s'') =[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	by(fastsimp elim:silent_moves_split)
      from snoc have "length as' < length as" by simp
      from `n\<^isub>c,kind \<turnstile> (ms'',s'') =[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
      have "n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')"
	by(fastsimp elim:silent_moves.cases)
      show ?thesis
      proof(cases "kind a'" rule:edge_kind_cases)
	case Intra
	with `n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')`
	have "valid_edge a'" and "m' = targetnode a'"
	  by(auto elim:silent_move.cases simp:intra_kind_def)
	from `n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')` `intra_kind (kind a')`
	have "ms'' = sourcenode a'#ms'"
	  by -(erule silent_move.cases,auto simp:intra_kind_def,(cases ms'',auto)+)
	with IH `length as' < length as` `n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (ms'',s'')`
	have "(\<exists>asx ax asx'. as' = asx @ ax # asx' \<and> (\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	  call_of_return_node (hd ms') (sourcenode ax) \<and> 
	  targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a') \<or> ms' = ms"
	  by simp blast
	thus ?thesis
	proof
	  assume "\<exists>asx ax asx'. as' = asx @ ax # asx' \<and> 
	    (\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	    call_of_return_node (hd ms') (sourcenode ax) \<and> 
	    targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'"
	  then obtain asx ax asx' where "as' = asx @ ax # asx'"
	    and "\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
	    and "call_of_return_node (hd ms') (sourcenode ax)"
	    and "targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'"
	    by blast
	  from `as' = asx @ ax # asx'` have "as'@[a'] = asx @ ax # (asx' @ [a'])"
	    by simp
	  moreover
	  from `targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'` `intra_kind (kind a')` 
	    `m' = targetnode a'` `valid_edge a'`
	  have "targetnode ax -asx'@[a']\<rightarrow>\<^bsub>sl\<^esub>* m'"
	    by(fastsimp intro:path_Append path_edge same_level_path_aux_Append 
	      upd_cs_Append simp:slp_def same_level_path_def intra_kind_def)
	  ultimately show ?thesis using `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	    `call_of_return_node (hd ms') (sourcenode ax)` snoc by blast
	next
	  assume "ms' = ms" thus ?thesis by simp
	qed
      next
	case (Call Q r p fs)
	with `n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')` obtain a''
	  where "valid_edge a'" and "a'' \<in> get_return_edges a'"
	  and "hd ms'' = sourcenode a'" and "m' = targetnode a'"
	  and "ms' = (targetnode a'')#tl ms''" and "length ms'' = length s''"
	  and "pred (kind a') s''"
	  by(auto elim:silent_move.cases simp:intra_kind_def)
	from `valid_edge a'` `a'' \<in> get_return_edges a'` have "valid_edge a''"
	  by(rule get_return_edges_valid)
	from `valid_edge a''` `valid_edge a'` `a'' \<in> get_return_edges a'`
	have "return_node (targetnode a'')" by(fastsimp simp:return_node_def)
	with `valid_edge a'` `valid_edge a''`
	  `a'' \<in> get_return_edges a'` `ms' = (targetnode a'')#tl ms''`
	have "call_of_return_node (hd ms') (sourcenode a')"
	  by(simp add:call_of_return_node_def) blast
	with snoc `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m' = targetnode a'` `valid_edge a'`
	show ?thesis by(fastsimp intro:empty_path simp:slp_def same_level_path_def)
      next
	case (Return Q p f)
	with `n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')` 
	have "valid_edge a'" and "hd ms'' = sourcenode a'"
	  and "hd(tl ms'') = targetnode a'" and "m'#ms' = tl ms''"
	  and "length ms'' = length s''" and "length s'' = Suc(length s')"
	  and "s' \<noteq> []"
	  by(auto elim:silent_move.cases simp:intra_kind_def)
	hence "ms'' = sourcenode a' # targetnode a' # ms'" by(cases ms'') auto
	with `length as' < length as` `n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (ms'',s'')` IH
	have "(\<exists>asx ax asx'. as' = asx @ ax # asx' \<and> (\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	  call_of_return_node (targetnode a') (sourcenode ax) \<and>
	  targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a') \<or> ms = targetnode a' # ms'"
	  apply - apply(erule_tac x="as'" in allE) apply clarsimp
	  apply(erule_tac x="sourcenode a'" in allE)
	  apply(erule_tac x="targetnode a' # ms'" in allE)
	  by fastsimp
	thus ?thesis
	proof
	  assume "\<exists>asx ax asx'. as' = asx @ ax # asx' \<and> 
	    (\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	    call_of_return_node (targetnode a') (sourcenode ax) \<and>
	    targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'"
	  then obtain asx ax asx' where "as' = asx @ ax # asx'"
	    and "\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
	    and "call_of_return_node (targetnode a') (sourcenode ax)"
	    and "targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'" by blast
	  from `as' = asx @ ax # asx'` snoc have"length asx < length as" by simp
	  moreover
	  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` snoc `as' = asx @ ax # asx'`
	  obtain msx sx where "n\<^isub>c,kind \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)"
	    and "n\<^isub>c,kind \<turnstile> (msx,sx) =ax#asx'@[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	    by(fastsimp elim:silent_moves_split)
	  from `n\<^isub>c,kind \<turnstile> (msx,sx) =ax#asx'@[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
	  obtain xs x ys y where "n\<^isub>c,kind \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (xs,x)"
	    and "n\<^isub>c,kind \<turnstile> (xs,x) =asx'\<Rightarrow>\<^isub>\<tau> (ys,y)"
	    and "n\<^isub>c,kind \<turnstile> (ys,y) =[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	    apply - apply(erule silent_moves.cases) apply auto
	    by(erule silent_moves_split) auto
	  from `n\<^isub>c,kind \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (xs,x)` `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	  obtain msx' ax' where "msx = sourcenode ax#msx'" 
	    and "ax' \<in> get_return_edges ax"
	    and [simp]:"xs = (targetnode ax)#(targetnode ax')#msx'"
	    and "length x = Suc(length sx)" and "length msx = length sx"
	    apply - apply(erule silent_move.cases) apply(auto simp:intra_kind_def)
	    by(cases msx,auto)+
	  from `n\<^isub>c,kind \<turnstile> (ys,y) =[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` obtain msy 
	    where "ys = sourcenode a'#msy"
	    apply - apply(erule silent_moves.cases) apply auto
	    apply(erule silent_move.cases)
	    by(cases ys,auto)+
	  with `n\<^isub>c,kind \<turnstile> (xs,x) =asx'\<Rightarrow>\<^isub>\<tau> (ys,y)` 
	    `targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'`
	    `xs = (targetnode ax)#(targetnode ax')#msx'`
	  have "(targetnode ax')#msx' = msy" apply simp
	    by(fastsimp intro:silent_moves_same_level_path)
	  with `n\<^isub>c,kind \<turnstile> (ys,y) =[a']\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `kind a' = Q\<^bsub>p\<^esub>\<hookleftarrow>f` 
	    `ys = sourcenode a'#msy`
	  have "m' = targetnode a'" and "msx' = ms'"
	    by(fastsimp elim:silent_moves.cases silent_move.cases 
	                simp:intra_kind_def)+
	  with `n\<^isub>c,kind \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)` `msx = sourcenode ax#msx'`
	  have "n\<^isub>c,kind \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (sourcenode ax#ms',sx)" by simp
	  ultimately have "(\<exists>xs x xs'. asx = xs@x#xs' \<and> 
	    (\<exists>Q r p fs. kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	    call_of_return_node (hd ms') (sourcenode x) \<and>
	    targetnode x -xs'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode ax) \<or> ms = ms'" using IH
	    by simp blast
	  thus ?thesis
	  proof
	    assume "\<exists>xs x xs'. asx = xs@x#xs' \<and> (\<exists>Q r p fs. kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
	      call_of_return_node (hd ms') (sourcenode x) \<and>
	      targetnode x -xs'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode ax"
	    then obtain xs x xs' where "asx = xs@x#xs'"
	      and "\<exists>Q r p fs. kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
	      and "call_of_return_node (hd ms') (sourcenode x)"
	      and "targetnode x -xs'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode ax" by blast
	    from `asx = xs@x#xs'` `as' = asx @ ax # asx'` snoc
	    have "as = xs@x#(xs'@ax#asx'@[a'])" by simp
	    from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `valid_node m` rest
	    have "m -as\<rightarrow>* m'" and "valid_path_aux cs as"
	      by(auto dest:silent_moves_vpa_path[of _ _ _ _ _ _ _ _ _ rs cs]
		      simp:valid_call_list_def valid_return_list_def targetnodes_def)
	    hence "m -as\<rightarrow>\<^isub>\<surd>* m'" 
	      by(fastsimp intro:valid_path_aux_valid_path simp:vp_def)
	    with snoc have "m -as'\<rightarrow>\<^isub>\<surd>* sourcenode a'"
	      by(auto elim:path_split_snoc dest:valid_path_aux_split 
		simp:vp_def valid_path_def)
	    with `as' = asx @ ax # asx'`
	    have "valid_edge ax" and "targetnode ax -asx'\<rightarrow>* sourcenode a'"
	      by(auto dest:path_split simp:vp_def)
	    hence "sourcenode ax -ax#asx'\<rightarrow>* sourcenode a'"
	      by(fastsimp intro:Cons_path)
	    from `valid_edge a'` have "sourcenode a' -[a']\<rightarrow>* targetnode a'"
	      by(rule path_edge)
	    with `sourcenode ax -ax#asx'\<rightarrow>* sourcenode a'`
	    have "sourcenode ax -(ax#asx')@[a']\<rightarrow>* targetnode a'"
	      by(rule path_Append)
	    from `m -as\<rightarrow>\<^isub>\<surd>* m'` snoc `as' = asx @ ax # asx'` snoc
	    have "valid_path_aux ([]@(upd_cs [] asx)) (ax # asx' @ [a'])"
	      by(fastsimp dest:valid_path_aux_split simp:vp_def valid_path_def)
	    hence "valid_path_aux [] (ax#asx'@[a'])" 
	      by(rule valid_path_aux_callstack_prefix)
	    with `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	    have "valid_path_aux [ax] (asx'@[a'])" by fastsimp
	    hence "valid_path_aux (upd_cs [ax] asx') [a']"
	      by(rule valid_path_aux_split)
	    from `targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'`
	    have "same_level_path_aux [] asx'" and "upd_cs [] asx' = []" 
	      by(simp_all add:slp_def same_level_path_def)
	    hence "upd_cs ([]@[ax]) asx' = []@[ax]"
	      by(rule same_level_path_upd_cs_callstack_Append)
	    with `valid_path_aux (upd_cs [ax] asx') [a']`
	    have "valid_path_aux [ax] [a']" by(simp del:valid_path_aux.simps)
	    with `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `kind a' = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	    have "a' \<in> get_return_edges ax" by simp
	    with `upd_cs ([]@[ax]) asx' = []@[ax]` `kind a' = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	    have "upd_cs [ax] (asx'@[a']) = []" by(fastsimp intro:upd_cs_Append)
	    with `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	    have "upd_cs [] (ax#asx'@[a']) = []" by fastsimp
	    from `targetnode ax -asx'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode a'`
	    have "same_level_path_aux [] asx'" and "upd_cs [] asx' = []" 
	      by(simp_all add:slp_def same_level_path_def)
	    hence "same_level_path_aux ([]@[ax]) asx'" 
	      by -(rule same_level_path_aux_callstack_Append)
	    with `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `kind a' = Q\<^bsub>p\<^esub>\<hookleftarrow>f` 
	      `a' \<in> get_return_edges ax` `upd_cs ([]@[ax]) asx' = []@[ax]`
	    have "same_level_path_aux [] ((ax#asx')@[a'])"
	      by(fastsimp intro:same_level_path_aux_Append)
	    with `upd_cs [] (ax#asx'@[a']) = []`
	      `sourcenode ax -(ax#asx')@[a']\<rightarrow>* targetnode a'`
	    have "sourcenode ax -(ax#asx')@[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'"
	      by(simp add:slp_def same_level_path_def)
	    with `targetnode x -xs'\<rightarrow>\<^bsub>sl\<^esub>* sourcenode ax`
	    have "targetnode x -xs'@((ax#asx')@[a'])\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'"
	      by(rule slp_Append)
	    with `\<exists>Q r p fs. kind x = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` 
	      `call_of_return_node (hd ms') (sourcenode x)`
	      `as = xs@x#(xs'@ax#asx'@[a'])` `m' = targetnode a'`
	    show ?thesis by simp blast
	  next
	    assume "ms = ms'" thus ?thesis by simp
	  qed
	next
	  assume "ms = targetnode a' # ms'"
	  from `n\<^isub>c,kind \<turnstile> (ms'',s'') -a'\<rightarrow>\<^isub>\<tau> (m'#ms',s')` `kind a' = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	    `ms'' = sourcenode a' # targetnode a' # ms'`
	  have "\<exists>m \<in> set (targetnode a' # ms'). \<exists>m'. call_of_return_node m m' \<and> 
	    m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
	    by(fastsimp elim!:silent_move.cases simp:intra_kind_def)
	  with `ms = targetnode a' # ms'` callstack
	  have False by fastsimp
	  thus ?thesis by simp
	qed
      qed
    qed
  qed
qed


lemma silent_moves_called_node_in_slice1_hd_nodestack_in_slice1:
  assumes "n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" and "valid_node m"
  and "CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c"
  and "\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" and "ms = targetnodes rs"
  and "valid_return_list rs m" and "length rs = length cs"
  obtains as' a as'' where "as = as'@a#as''" and "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "call_of_return_node (hd ms') (sourcenode a)"
  and "targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'" and "CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c"
  | "ms' = ms"
proof(atomize_elim)
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `valid_node m`
    `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `ms = targetnodes rs`
    `valid_return_list rs m` `length rs = length cs`
  have "m -as\<rightarrow>* m'"
    by(auto dest:silent_moves_vpa_path[of _ _ _ _ _ _ _ _ _ rs cs]
	    simp:valid_call_list_def valid_return_list_def targetnodes_def)
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `valid_node m`
    `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `ms = targetnodes rs`
    `valid_return_list rs m` `length rs = length cs`
  show "(\<exists>as' a as''. as = as' @ a # as'' \<and> (\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
    call_of_return_node (hd ms') (sourcenode a) \<and> targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m' \<and>
    CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c) \<or> ms' = ms"
  proof(rule silent_moves_call_edge)
    fix as' a as'' assume "as = as'@a#as''" and "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "call_of_return_node (hd ms') (sourcenode a)"
      and "targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'"
    from `\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain Q r p fs 
      where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by blast
    from `targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'` obtain asx where "targetnode a -asx\<rightarrow>\<^isub>\<iota>* m'"
      by -(erule same_level_path_inner_path)
    from `m -as\<rightarrow>* m'` `as = as'@a#as''` have "valid_edge a"
      by(fastsimp dest:path_split simp:vp_def)
    have "m' \<noteq> (_Exit_)"
    proof
      assume "m' = (_Exit_)"
      have "get_proc (_Exit_) = Main" by(rule get_proc_Exit)
      from `targetnode a -asx\<rightarrow>\<^isub>\<iota>* m'`
      have "get_proc (targetnode a) = get_proc m'" by(rule intra_path_get_procs)
      with `m' = (_Exit_)` `get_proc (_Exit_) = Main`
      have "get_proc (targetnode a) = Main" by simp
      with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge a`
      have "kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by(fastsimp dest:get_proc_call)
      with `valid_edge a` show False by(rule Main_no_call_target)
    qed
    show ?thesis
    proof(cases "targetnode a = m'")
      case True
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node m'"
	by(fastsimp intro:sum_SDG_call_edge)
      with `CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c`
      have "CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c" by -(rule call_slice1)
      with `as = as'@a#as''` `\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	`call_of_return_node (hd ms') (sourcenode a)`
	`targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'` show ?thesis by blast
    next
      case False
      with `targetnode a -asx\<rightarrow>\<^isub>\<iota>* m'` `m' \<noteq> (_Exit_)` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      obtain ns where "CFG_node (targetnode a) cd-ns\<rightarrow>\<^isub>d* CFG_node m'"
	by(fastsimp elim!:in_proc_cdep_SDG_path)
      hence "CFG_node (targetnode a) is-ns\<rightarrow>\<^isub>d* CFG_node m'"
	by(fastsimp intro:intra_SDG_path_is_SDG_path cdep_SDG_path_intra_SDG_path)
      with `CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c`
      have "CFG_node (targetnode a) \<in> sum_SDG_slice1 n\<^isub>c"
	by -(rule is_SDG_path_slice1)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)"
	by(fastsimp intro:sum_SDG_call_edge)
      with `CFG_node (targetnode a) \<in> sum_SDG_slice1 n\<^isub>c`
      have "CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c" by -(rule call_slice1)
      with `as = as'@a#as''` `\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	`call_of_return_node (hd ms') (sourcenode a)`
	`targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'` show ?thesis by blast
    qed
  next
    assume "ms' = ms" thus ?thesis by simp
  qed
qed


lemma silent_moves_called_node_in_slice1_nodestack_in_slice1:
  "\<lbrakk>n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s'); valid_node m; 
   CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c;
   \<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
   \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); ms = targetnodes rs;
   valid_return_list rs m; length rs = length cs\<rbrakk>
  \<Longrightarrow> \<forall>mx \<in> set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
proof(induct ms' arbitrary:as m' s')
  case (Cons mx msx)
  note IH = `\<And>as m' s'. \<lbrakk>n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # msx,s'); valid_node m; 
    CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c;
   \<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
   \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); ms = targetnodes rs;
   valid_return_list rs m; length rs = length cs\<rbrakk>
    \<Longrightarrow> \<forall>mx\<in>set msx. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` `valid_node m`
    `CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c` 
    `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `ms = targetnodes rs`
    `valid_return_list rs m` `length rs = length cs`
  show ?case
  proof(rule silent_moves_called_node_in_slice1_hd_nodestack_in_slice1)
    fix as' a as'' assume "as = as'@a#as''" and "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "call_of_return_node (hd (mx # msx)) (sourcenode a)" 
      and "CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c"
      and "targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'"
    from `CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c`
    have "sourcenode a \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastsimp intro:combSlice_refl simp:SDG_to_CFG_set_def HRB_slice_def)
    from `n\<^isub>c,kind \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` `as = as'@a#as''`
    obtain xs x where "n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (xs,x)"
      and "n\<^isub>c,kind \<turnstile> (xs,x) =a#as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')"
      by(fastsimp elim:silent_moves_split)
    from `n\<^isub>c,kind \<turnstile> (xs,x) =a#as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')`
    obtain ys y where "n\<^isub>c,kind \<turnstile> (xs,x) -a\<rightarrow>\<^isub>\<tau> (ys,y)"
      and "n\<^isub>c,kind \<turnstile> (ys,y) =as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')"
      by(fastsimp elim:silent_moves.cases)
    from `n\<^isub>c,kind \<turnstile> (xs,x) -a\<rightarrow>\<^isub>\<tau> (ys,y)` `\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain xs' a' where "xs = sourcenode a#xs'" 
      and "ys = targetnode a#targetnode a'#xs'"
      apply - apply(erule silent_move.cases) apply(auto simp:intra_kind_def)
      by(cases xs,auto)+
    from `n\<^isub>c,kind \<turnstile> (ys,y) =as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` 
      `ys = targetnode a#targetnode a'#xs'` `targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'`
    have "mx = targetnode a'" and "xs' = msx" 
      by(auto dest:silent_moves_same_level_path)
    with `xs = sourcenode a#xs'` `n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (xs,x)`
    have "n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (sourcenode a#msx,x)" by simp
    from IH[OF `n\<^isub>c,kind \<turnstile> (m#ms,s) =as'\<Rightarrow>\<^isub>\<tau> (sourcenode a#msx,x)` 
      `valid_node m` `CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c`
      `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
      `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `ms = targetnodes rs`
      `valid_return_list rs m` `length rs = length cs`]
    have callstack:"\<forall>mx\<in>set msx.
      \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" .
    with `as = as'@a#as''` `call_of_return_node (hd (mx # msx)) (sourcenode a)` 
      `sourcenode a \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` show ?thesis by fastsimp
  next
    assume "mx # msx = ms"
    with `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    show ?thesis by fastsimp
  qed
qed simp


lemma silent_moves_slice_intra_path:
  assumes "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
  and "\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  shows "\<forall>a \<in> set as. intra_kind (kind a)"
proof(rule ccontr)
  assume "\<not> (\<forall>a\<in>set as. intra_kind (kind a))"
  hence "\<exists>a \<in> set as. \<not> intra_kind (kind a)" by fastsimp
  then obtain asx ax asx' where "as = asx@ax#asx'" 
    and "\<forall>a\<in>set asx. intra_kind (kind a)" and "\<not> intra_kind (kind ax)"
    by(fastsimp elim!:split_list_first_propE)
  from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `as = asx@ax#asx'`
  obtain msx sx msx' sx' where "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)"
    and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (msx',sx')"
    and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (msx',sx') =asx'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
    by(auto elim!:silent_moves_split elim:silent_moves.cases)
  from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (msx',sx')` obtain xs
    where [simp]:"msx = sourcenode ax#xs" by(cases msx)(auto elim:silent_move.cases)
  from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)` `\<forall>a\<in>set asx. intra_kind (kind a)`
  have [simp]:"xs = ms" by(fastsimp dest:silent_moves_intra_path)
  show False
  proof(cases "kind ax" rule:edge_kind_cases)
    case Intra with `\<not> intra_kind (kind ax)` show False by simp
  next
    case (Call Q r p fs)
    with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (msx',sx')` 
      `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    have "sourcenode ax \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" and "pred (slice_kind n\<^isub>c ax) sx"
      by(auto elim!:silent_move.cases simp:intra_kind_def)
    from `sourcenode ax \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "slice_kind n\<^isub>c ax = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>replicate (length fs) empty"
      by(rule slice_kind_Call)
    with `pred (slice_kind n\<^isub>c ax) sx` show False by(cases sx) auto
  next
    case (Return Q p f)
    with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (msx,sx) -ax\<rightarrow>\<^isub>\<tau> (msx',sx')` 
      `\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    show False by(fastsimp elim!:silent_move.cases simp:intra_kind_def)
  qed
qed


lemma silent_moves_slice_keeps_state:
  assumes "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
  and "\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  shows "s = s'"
proof -
  from assms have "\<forall>a \<in> set as. intra_kind (kind a)"
    by(rule silent_moves_slice_intra_path)
  with assms show ?thesis
  proof(induct n\<^isub>c f\<equiv>"slice_kind n\<^isub>c" msx\<equiv>"m#ms" s as msx'\<equiv>"m'#ms'" s'
        arbitrary:m rule:silent_moves.induct)
    case (silent_moves_Nil msx sx n\<^isub>c f m) thus ?case by simp
  next
    case (silent_moves_Cons n\<^isub>c f msx sx a msx' sx' as ms'' s'' m)
    note IH = `\<And>m.
      \<lbrakk>\<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      \<forall>a\<in>set as. intra_kind (kind a); f = slice_kind n\<^isub>c; msx' = m # ms;
      ms'' = m' # ms'\<rbrakk> \<Longrightarrow> sx' = s''`
    note callstack = `\<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    from `\<forall>a\<in>set (a # as). intra_kind (kind a)` have "intra_kind (kind a)"
      and "\<forall>a\<in>set as. intra_kind (kind a)" by simp_all
    from `n\<^isub>c,f \<turnstile> (msx,sx) -a\<rightarrow>\<^isub>\<tau> (msx',sx')` `intra_kind (kind a)` `msx = m # ms`
      `f = slice_kind n\<^isub>c` callstack
    have [simp]:"msx' = targetnode a#ms" and "sx' = transfer (slice_kind n\<^isub>c a) sx"
      and "sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" and "valid_edge a" and "sx \<noteq> []"
      by(auto elim!:silent_move.cases simp:intra_kind_def)
    from IH[OF callstack `\<forall>a\<in>set as. intra_kind (kind a)` `f = slice_kind n\<^isub>c` 
      `msx' = targetnode a#ms` `ms'' = m' # ms'`] have "sx' = s''" .
    from `intra_kind (kind a)`
    have "sx = sx'"
    proof(cases "kind a")
      case (UpdateEdge f')
      with `sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
      have "slice_kind n\<^isub>c a = \<Up>id" by(rule slice_kind_Upd)
      with `sx' = transfer (slice_kind n\<^isub>c a) sx` `sx \<noteq> []`
      show ?thesis by(cases sx) auto
    next
      case (PredicateEdge Q)
      with `sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `valid_edge a`
      obtain Q' where "slice_kind n\<^isub>c a = (Q')\<^isub>\<surd>"
	by -(erule kind_Predicate_notin_slice_slice_kind_Predicate)
      with `sx' = transfer (slice_kind n\<^isub>c a) sx` `sx \<noteq> []`
      show ?thesis by(cases sx) auto
    qed (auto simp:intra_kind_def)
    with `sx' = s''` show ?case by simp
  qed
qed


subsection {* Definition of @{text "slice_edges"} *}

definition slice_edge :: "'node SDG_node \<Rightarrow> 'edge list \<Rightarrow> 'edge \<Rightarrow> bool"
where "slice_edge n\<^isub>c cs a \<equiv> (\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<and>
  (case (kind a) of Q\<^bsub>p\<^esub>\<hookleftarrow>f \<Rightarrow> True | _ \<Rightarrow> sourcenode a \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)"


lemma silent_move_no_slice_edge:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (ms,s) -a\<rightarrow>\<^isub>\<tau> (ms',s'); tl ms = targetnodes rs; length rs = length cs;
    \<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))\<rbrakk>
  \<Longrightarrow> \<not> slice_edge n\<^isub>c cs a"
proof(induct rule:silent_move.induct)
  case (silent_move_intra f a s s' ms n\<^isub>c ms')
  note disj = `(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)
    \<or> hd ms \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  from disj show ?case
  proof
    assume "\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    with `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
      `length (tl ms) = length cs`
    have "\<exists>c \<in> set cs. sourcenode c \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      apply(auto simp:in_set_conv_nth)
      by(erule_tac x="i" in allE) auto
    thus ?thesis by(auto simp:slice_edge_def)
  next
    assume "hd ms \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    with `hd ms = sourcenode a` `intra_kind (kind a)`
    show ?case by(auto simp:slice_edge_def simp:intra_kind_def)
  qed
next
  case (silent_move_call f a s s' Q r p fs a' ms n\<^isub>c ms')
  note disj = `(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)
    \<or> hd ms \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  from disj show ?case
  proof
    assume "\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    with `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
      `length (tl ms) = length cs`
    have "\<exists>c \<in> set cs. sourcenode c \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      apply(auto simp:in_set_conv_nth)
      by(erule_tac x="i" in allE) auto
    thus ?thesis by(auto simp:slice_edge_def)
  next
    assume "hd ms \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    with `hd ms = sourcenode a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    show ?case by(auto simp:slice_edge_def)
  qed
next
  case (silent_move_return f a s s' Q p f' ms n\<^isub>c ms')
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  from `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
    `\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `length (tl ms) = length cs`
  have "\<exists>c \<in> set cs. sourcenode c \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    apply(auto simp:in_set_conv_nth)
    by(erule_tac x="i" in allE) auto
  thus ?case by(auto simp:slice_edge_def)
qed


lemma observable_move_slice_edge:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s'); tl ms = targetnodes rs; length rs = length cs;
    \<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))\<rbrakk>
  \<Longrightarrow> slice_edge n\<^isub>c cs a"
proof(induct rule:observable_move.induct)
  case (observable_move_intra f a s s' ms n\<^isub>c ms')
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  with `\<forall>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `\<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))`
  have "\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    apply(auto simp:in_set_conv_nth)
    by(erule_tac x="i" in allE) auto
  with `hd ms = sourcenode a` `hd ms \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `intra_kind (kind a)`
  show ?case by(auto simp:slice_edge_def simp:intra_kind_def)
next
  case (observable_move_call f a s s' Q r p fs a' ms n\<^isub>c ms')
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  with `\<forall>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `\<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))`
  have "\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    apply(auto simp:in_set_conv_nth)
    by(erule_tac x="i" in allE) auto
  with `hd ms = sourcenode a` `hd ms \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  show ?case by(auto simp:slice_edge_def)
next
  case (observable_move_return f a s s' Q p f' ms n\<^isub>c ms')
  from `pred (f a) s` `length ms = length s` obtain x xs where "ms = x#xs"
    by(cases ms) auto
  from `length rs = length cs` `tl ms = targetnodes rs`
  have "length (tl ms) = length cs" by(simp add:targetnodes_def)
  with `\<forall>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    `\<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))`
  have "\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    apply(auto simp:in_set_conv_nth)
    by(erule_tac x="i" in allE) auto
  with `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` show ?case by(auto simp:slice_edge_def)
qed



function slice_edges :: "'node SDG_node \<Rightarrow> 'edge list \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
where "slice_edges n\<^isub>c cs [] = []"
  | "slice_edge n\<^isub>c cs a \<Longrightarrow> 
     slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c (upd_cs cs [a]) as"
  | "\<not> slice_edge n\<^isub>c cs a \<Longrightarrow> 
     slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c (upd_cs cs [a]) as"
by(atomize_elim)(auto,case_tac b,auto)
termination by(lexicographic_order)


lemma slice_edges_Append:
  "\<lbrakk>slice_edges n\<^isub>c cs as = as'; slice_edges n\<^isub>c (upd_cs cs as) asx = asx'\<rbrakk>
  \<Longrightarrow> slice_edges n\<^isub>c cs (as@asx) = as'@asx'"
proof(induct as arbitrary:cs as')
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note IH = `\<And>cs as'. \<lbrakk>slice_edges n\<^isub>c cs xs = as'; 
    slice_edges n\<^isub>c (upd_cs cs xs) asx = asx'\<rbrakk>
    \<Longrightarrow> slice_edges n\<^isub>c cs (xs @ asx) = as' @ asx'`
  from `slice_edges n\<^isub>c (upd_cs cs (x # xs)) asx = asx'` 
  have "slice_edges n\<^isub>c (upd_cs (upd_cs cs [x]) xs) asx = asx'"
    by(cases "kind x")(auto,cases cs,auto)
  show ?case
  proof(cases "slice_edge n\<^isub>c cs x")
    case True
    with `slice_edges n\<^isub>c cs (x # xs) = as'`
    have "x#slice_edges n\<^isub>c (upd_cs cs [x]) xs = as'" by simp
    then obtain xs' where "as' = x#xs'"
      and "slice_edges n\<^isub>c (upd_cs cs [x]) xs = xs'" by(cases as') auto
    from IH[OF `slice_edges n\<^isub>c (upd_cs cs [x]) xs = xs'`
      `slice_edges n\<^isub>c (upd_cs (upd_cs cs [x]) xs) asx = asx'`]
    have "slice_edges n\<^isub>c (upd_cs cs [x]) (xs @ asx) = xs' @ asx'" .
    with True `as' = x#xs'` show ?thesis by simp
  next
    case False
    with `slice_edges n\<^isub>c cs (x # xs) = as'`
    have "slice_edges n\<^isub>c (upd_cs cs [x]) xs = as'" by simp
    from IH[OF this `slice_edges n\<^isub>c (upd_cs (upd_cs cs [x]) xs) asx = asx'`]
    have "slice_edges n\<^isub>c (upd_cs cs [x]) (xs @ asx) = as' @ asx'" .
    with False show ?thesis by simp
  qed
qed


lemma slice_edges_Nil_split:
  "slice_edges n\<^isub>c cs (as@as') = []
  \<Longrightarrow> slice_edges n\<^isub>c cs as = [] \<and> slice_edges n\<^isub>c (upd_cs cs as) as' = []"
apply(induct as arbitrary:cs)
 apply clarsimp
apply(case_tac "slice_edge n\<^isub>c cs a") apply auto
apply(case_tac "kind a") apply auto
apply(case_tac cs) apply auto
done


lemma slice_intra_edges_no_nodes_in_slice:
  "\<lbrakk>slice_edges n\<^isub>c cs as = []; \<forall>a \<in> set as. intra_kind (kind a);
    \<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> \<forall>nx \<in> set(sourcenodes as). nx \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
proof(induct as)
  case Nil thus ?case by(fastsimp simp:sourcenodes_def)
next
  case (Cons a' as')
  note IH = ` \<lbrakk>slice_edges n\<^isub>c cs as' = []; \<forall>a\<in>set as'. intra_kind (kind a);
    \<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
    \<Longrightarrow> \<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  from `\<forall>a\<in>set (a' # as'). intra_kind (kind a)`
  have "intra_kind (kind a')" and "\<forall>a\<in>set as'. intra_kind (kind a)" by simp_all
  from `slice_edges n\<^isub>c cs (a' # as') = []` `intra_kind (kind a')`
    `\<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  have "sourcenode a' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" and "slice_edges n\<^isub>c cs as' = []"
    by(cases "slice_edge n\<^isub>c cs a'",auto simp:intra_kind_def slice_edge_def)+
  from IH[OF `slice_edges n\<^isub>c cs as' = []` `\<forall>a\<in>set as'. intra_kind (kind a)`
    `\<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`] 
  have "\<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" .
  with `sourcenode a' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` show ?case by(simp add:sourcenodes_def)
qed


lemma silent_moves_no_slice_edges:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow>\<^isub>\<tau> (ms',s'); tl ms = targetnodes rs; length rs = length cs;
    \<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))\<rbrakk>
  \<Longrightarrow> slice_edges n\<^isub>c cs as = [] \<and> (\<exists>rs'. tl ms' = targetnodes rs' \<and>
  length rs' = length (upd_cs cs as) \<and> (\<forall>i<length (upd_cs cs as). 
  call_of_return_node (tl ms'!i) (sourcenode ((upd_cs cs as)!i))))"
proof(induct arbitrary:rs cs rule:silent_moves.induct)
  case (silent_moves_Cons n\<^isub>c f ms s a ms' s' as ms'' s'')
  from `n\<^isub>c,f \<turnstile> (ms,s) -a\<rightarrow>\<^isub>\<tau> (ms',s')` `tl ms = targetnodes rs` `length rs = length cs`
    `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
  have "\<not> slice_edge n\<^isub>c cs a" by(rule silent_move_no_slice_edge)
  with silent_moves_Cons show ?case
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' ms n\<^isub>c ms')
    note IH = `\<And>rs cs. \<lbrakk>tl ms' = targetnodes rs; length rs = length cs;
      \<forall>i<length cs. call_of_return_node (tl ms' ! i) (sourcenode (cs ! i))\<rbrakk>
      \<Longrightarrow> slice_edges n\<^isub>c cs as = [] \<and> (\<exists>rs'. tl ms'' = targetnodes rs' \<and>
      length rs' = length (upd_cs cs as) \<and> (\<forall>i<length (upd_cs cs as).
      call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs cs as ! i))))`
    from `ms' = targetnode a # tl ms` `tl ms = targetnodes rs`
    have "tl ms' = targetnodes rs" by simp
    from `ms' = targetnode a # tl ms` `tl ms = targetnodes rs`
      `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
    have "\<forall>i<length cs. call_of_return_node (tl ms' ! i) (sourcenode (cs ! i))"
      by simp
    from IH[OF `tl ms' = targetnodes rs` `length rs = length cs` this]
    have "slice_edges n\<^isub>c cs as = []" 
      and "\<exists>rs'. tl ms'' = targetnodes rs' \<and> length rs' = length (upd_cs cs as) \<and>
      (\<forall>i<length (upd_cs cs as). 
      call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs cs as ! i)))" by simp_all
    with `intra_kind (kind a)` `\<not> slice_edge n\<^isub>c cs a`
    show ?case by(fastsimp simp:intra_kind_def)
  next
    case (silent_move_call f a s s' Q r p fs a' ms n\<^isub>c ms')
    note IH = `\<And>rs cs. \<lbrakk>tl ms' = targetnodes rs; length rs = length cs;
      \<forall>i<length cs. call_of_return_node (tl ms' ! i) (sourcenode (cs ! i))\<rbrakk>
      \<Longrightarrow> slice_edges n\<^isub>c cs as = [] \<and> (\<exists>rs'. tl ms'' = targetnodes rs' \<and>
      length rs' = length (upd_cs cs as) \<and> (\<forall>i<length (upd_cs cs as).
      call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs cs as ! i))))`
    from `tl ms = targetnodes rs` `ms' = targetnode a # targetnode a' # tl ms`
    have "tl ms' = targetnodes (a'#rs)" by(simp add:targetnodes_def)
    from `length rs = length cs` have "length (a'#rs) = length (a#cs)" by simp
    from `valid_edge a'` `valid_edge a` `a' \<in> get_return_edges a`
    have "return_node (targetnode a')" by(fastsimp simp:return_node_def)
    with `valid_edge a` `valid_edge a'` `a' \<in> get_return_edges a`
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(simp add:call_of_return_node_def) blast
    with `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
      `ms' = targetnode a # targetnode a' # tl ms`
    have "\<forall>i<length (a#cs). 
      call_of_return_node (tl ms' ! i) (sourcenode ((a#cs) ! i))"
      by auto (case_tac i,auto)
    from IH[OF `tl ms' = targetnodes (a'#rs)` `length (a'#rs) = length (a#cs)` this]
    have "slice_edges n\<^isub>c (a # cs) as = []"
      and "\<exists>rs'. tl ms'' = targetnodes rs' \<and>
      length rs' = length (upd_cs (a # cs) as) \<and>
      (\<forall>i<length (upd_cs (a # cs) as).
        call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs (a # cs) as ! i)))"
      by simp_all
    with `\<not> slice_edge n\<^isub>c cs a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?case by simp
  next
    case (silent_move_return f a s s' Q p f' ms n\<^isub>c ms')
    note IH = `\<And>rs cs. \<lbrakk>tl ms' = targetnodes rs; length rs = length cs;
      \<forall>i<length cs. call_of_return_node (tl ms' ! i) (sourcenode (cs ! i))\<rbrakk>
      \<Longrightarrow> slice_edges n\<^isub>c cs as = [] \<and> (\<exists>rs'. tl ms'' = targetnodes rs' \<and>
      length rs' = length (upd_cs cs as) \<and> (\<forall>i<length (upd_cs cs as).
      call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs cs as ! i))))`
    from `length s = Suc (length s')` `s' \<noteq> []` `length ms = length s` `ms' = tl ms`
    obtain x xs where [simp]:"ms' = x#xs" by(cases ms)(auto,case_tac ms',auto)
    from `ms' = tl ms` `tl ms = targetnodes rs` obtain r' rs' where "rs = r'#rs'"
      and "x = targetnode r'" and "tl ms' = targetnodes rs'"
      by(cases rs)(auto simp:targetnodes_def)
    from `length rs = length cs` `rs = r'#rs'` obtain c' cs' where "cs = c'#cs'"
      and "length rs' = length cs'" by(cases cs) auto
    from `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
      `cs = c'#cs'` `ms' = tl ms`
    have "\<forall>i<length cs'. call_of_return_node (tl ms' ! i) (sourcenode (cs' ! i))"
      by auto(erule_tac x="Suc i" in allE,cases "tl ms",auto)
    from IH[OF `tl ms' = targetnodes rs'` `length rs' = length cs'` this]
    have "slice_edges n\<^isub>c cs' as = []" and "\<exists>rs'. tl ms'' = targetnodes rs' \<and>
      length rs' = length (upd_cs cs' as) \<and> (\<forall>i<length (upd_cs cs' as).
      call_of_return_node (tl ms'' ! i) (sourcenode (upd_cs cs' as ! i)))"
      by simp_all
    with `\<not> slice_edge n\<^isub>c cs a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f'` `cs = c'#cs'`
    show ?case by simp
  qed
qed fastsimp



lemma observable_moves_singular_slice_edge:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s'); tl ms = targetnodes rs; length rs = length cs;
    \<forall>i<length cs. call_of_return_node (tl ms!i) (sourcenode (cs!i))\<rbrakk>
  \<Longrightarrow> slice_edges n\<^isub>c cs as = [last as]"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc n\<^isub>c f ms s as ms' s' a ms'' s'')
  from `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow>\<^isub>\<tau> (ms',s')` `tl ms = targetnodes rs` `length rs = length cs`
    `\<forall>i<length cs. call_of_return_node (tl ms ! i) (sourcenode (cs ! i))`
  obtain rs' where "slice_edges n\<^isub>c cs as = []" 
    and "tl ms' = targetnodes rs'" and "length rs' = length (upd_cs cs as)"
    and "\<forall>i<length (upd_cs cs as). 
    call_of_return_node (tl ms'!i) (sourcenode ((upd_cs cs as)!i))"
    by(fastsimp dest!:silent_moves_no_slice_edges)
  from `n\<^isub>c,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')` this
  have "slice_edge n\<^isub>c (upd_cs cs as) a" by -(rule observable_move_slice_edge)
  with `slice_edges n\<^isub>c cs as = []` have "slice_edges n\<^isub>c cs (as @ [a]) = []@[a]"
    by(fastsimp intro:slice_edges_Append)
  thus ?case by simp
qed


lemma silent_moves_nonempty_nodestack_False:
  assumes "n\<^isub>c,kind \<turnstile> ([m],[cf]) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" and "valid_node m"
  and "ms' \<noteq> []" and "CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c"
  shows False
proof -
  from assms have "slice_edges n\<^isub>c [] as \<noteq> []"
  proof(induct ms' arbitrary:as m' s')
    case (Cons mx msx)
    note IH = `\<And>as m' s'. \<lbrakk>n\<^isub>c,kind \<turnstile> ([m],[cf]) =as\<Rightarrow>\<^isub>\<tau> (m' # msx,s'); valid_node m; 
      msx \<noteq> []; CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c\<rbrakk>
      \<Longrightarrow> slice_edges n\<^isub>c [] as \<noteq> []`
    from `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` `valid_node m`
      `CFG_node m' \<in> sum_SDG_slice1 n\<^isub>c`
    obtain as' a as'' where "as = as'@a#as''" and "\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      and "call_of_return_node mx (sourcenode a)" 
      and "CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c"
      and "targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'"
      by(fastsimp elim!:silent_moves_called_node_in_slice1_hd_nodestack_in_slice1
      [of _ _ _ _ _ _ _ _ "[]" "[]"] simp:targetnodes_def valid_return_list_def)
    from `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` `as = as'@a#as''`
    obtain xs x where "n\<^isub>c,kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (xs,x)"
      and "n\<^isub>c,kind \<turnstile> (xs,x) =a#as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')"
      by(fastsimp elim:silent_moves_split)
    from `n\<^isub>c,kind \<turnstile> (xs,x) =a#as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')`
    obtain ys y where "n\<^isub>c,kind \<turnstile> (xs,x) -a\<rightarrow>\<^isub>\<tau> (ys,y)"
      and "n\<^isub>c,kind \<turnstile> (ys,y) =as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')"
      by(fastsimp elim:silent_moves.cases)
    from `n\<^isub>c,kind \<turnstile> (xs,x) -a\<rightarrow>\<^isub>\<tau> (ys,y)` `\<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain xs' a' where "xs = sourcenode a#xs'" 
      and "ys = targetnode a#targetnode a'#xs'"
      apply - apply(erule silent_move.cases) apply(auto simp:intra_kind_def)
      by(cases xs,auto)+
    from `n\<^isub>c,kind \<turnstile> (ys,y) =as''\<Rightarrow>\<^isub>\<tau> (m' # mx # msx,s')` 
      `ys = targetnode a#targetnode a'#xs'` `targetnode a -as''\<rightarrow>\<^bsub>sl\<^esub>* m'`
    have "mx = targetnode a'" and "xs' = msx"
      by(auto dest:silent_moves_same_level_path)
    with `xs = sourcenode a#xs'` `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (xs,x)`
    have "n\<^isub>c,kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (sourcenode a#msx,x)" by simp
    show ?case
    proof(cases "msx = []")
      case True
      from `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (sourcenode a#msx,x)`
      obtain rs' where "msx = targetnodes rs' \<and> length rs' = length (upd_cs [] as')"
	by(fastsimp dest!:silent_moves_no_slice_edges[where cs="[]" and rs="[]"]
	            simp:targetnodes_def)
      with True have "upd_cs [] as' = []"  by(cases rs')(auto simp:targetnodes_def)
      with `CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c` 
      have "slice_edge n\<^isub>c (upd_cs [] as') a"
	by(cases "kind a",auto intro:combSlice_refl 
	  simp:slice_edge_def SDG_to_CFG_set_def HRB_slice_def)
      hence "slice_edges n\<^isub>c (upd_cs [] as') (a#as'') \<noteq> []" by simp
      with `as = as'@a#as''` show ?thesis by(fastsimp dest:slice_edges_Nil_split)
    next
      case False
      from IH[OF `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (sourcenode a#msx,x)` 
	`valid_node m` this `CFG_node (sourcenode a) \<in> sum_SDG_slice1 n\<^isub>c`]
      have "slice_edges n\<^isub>c [] as' \<noteq> []" .
      with `as = as'@a#as''` show ?thesis by(fastsimp dest:slice_edges_Nil_split)
    qed
  qed simp
  moreover
  from `n\<^isub>c,kind \<turnstile> ([m],[cf]) =as\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` have "slice_edges n\<^isub>c [] as = []"
    by(fastsimp dest!:silent_moves_no_slice_edges[where cs="[]" and rs="[]"] 
	        simp:targetnodes_def)
  ultimately show False by simp
qed



lemma transfers_intra_slice_kinds_slice_edges:
  "\<lbrakk>\<forall>a \<in> set as. intra_kind (kind a); \<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as)) s =
  transfers (slice_kinds n\<^isub>c as) s"
proof(induct as arbitrary:s)
  case Nil thus ?case by(simp add:slice_kinds_def)
next
  case (Cons a' as')
  note IH = `\<And>s. \<lbrakk>\<forall>a\<in>set as'. intra_kind (kind a);
    \<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk> \<Longrightarrow>
    transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as')) s =
    transfers (slice_kinds n\<^isub>c as') s`
  from `\<forall>a\<in>set (a' # as'). intra_kind (kind a)`
  have "intra_kind (kind a')" and "\<forall>a\<in>set as'. intra_kind (kind a)"
    by simp_all
  show ?case
  proof(cases "slice_edge n\<^isub>c cs a'")
    case True
    with `intra_kind (kind a')`
    have eq:"transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs (a'#as'))) s
            = transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as')) 
                (transfer (slice_kind n\<^isub>c a') s)"
      by(cases "kind a'")(auto simp:slice_kinds_def intra_kind_def)
    have "transfers (slice_kinds n\<^isub>c (a'#as')) s
        = transfers (slice_kinds n\<^isub>c as') (transfer (slice_kind n\<^isub>c a') s)"
      by(simp add:slice_kinds_def)
    with eq IH[OF `\<forall>a\<in>set as'. intra_kind (kind a)` 
      `\<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`,
      of "transfer (slice_kind n\<^isub>c a') s"]
    show ?thesis by simp
  next
    case False
    with `intra_kind (kind a')`
    have eq:"transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs (a'#as'))) s
            = transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as')) s"
      by(cases "kind a'")(auto simp:slice_kinds_def intra_kind_def)
    from False `intra_kind (kind a')` `\<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    have "sourcenode a' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastsimp simp:slice_edge_def intra_kind_def)
    with `intra_kind (kind a')` have "transfer (slice_kind n\<^isub>c a') s = s"
      by(cases s)(auto,cases "kind a'",
	auto simp:slice_kind_def Let_def intra_kind_def)
    hence "transfers (slice_kinds n\<^isub>c (a'#as')) s
         = transfers (slice_kinds n\<^isub>c as') s"
      by(simp add:slice_kinds_def)
    with eq IH[OF `\<forall>a\<in>set as'. intra_kind (kind a)` 
      `\<forall>c\<in>set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`,of s] show ?thesis by simp
  qed
qed



lemma exists_sliced_intra_path_preds:
  assumes "m -as\<rightarrow>\<^isub>\<iota>* m'" and "slice_edges n\<^isub>c cs as = []" 
  and "m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  obtains as' where "m -as'\<rightarrow>\<^isub>\<iota>* m'" and "preds (slice_kinds n\<^isub>c as') (cf#cfs)"
  and "slice_edges n\<^isub>c cs as' = []"
proof(atomize_elim)
  from `m -as\<rightarrow>\<^isub>\<iota>* m'` have "m -as\<rightarrow>* m'" and "\<forall>a \<in> set as. intra_kind(kind a)"
    by(simp_all add:intra_path_def)
  from `slice_edges n\<^isub>c cs as = []` `\<forall>a \<in> set as. intra_kind(kind a)`
    `\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
  have "\<forall>nx \<in> set(sourcenodes as). nx \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    by(rule slice_intra_edges_no_nodes_in_slice)
  with `m -as\<rightarrow>\<^isub>\<iota>* m'` `m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` have "m' \<in> obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastsimp intro:obs_intra_elem)
  hence "obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}" by(rule obs_intra_singleton_element)
  from `m -as\<rightarrow>* m'` have "valid_node m" and "valid_node m'"
    by(fastsimp dest:path_valid_node)+
  from `m -as\<rightarrow>\<^isub>\<iota>* m'` obtain x where "distance m m' x" and "x \<le> length as"
    by(erule every_path_distance)
  from `distance m m' x` `obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}`
  show "\<exists>as'. m -as'\<rightarrow>\<^isub>\<iota>* m' \<and> preds (slice_kinds n\<^isub>c as') (cf#cfs) \<and> 
	      slice_edges n\<^isub>c cs as' = []"
  proof(induct x arbitrary:m rule:nat.induct)
    case zero
    from `distance m m' 0` have "m = m'"
      by(fastsimp elim:distance.cases simp:intra_path_def)
    with `valid_node m'` show ?case
      by(rule_tac x="[]" in exI,
        auto intro:empty_path simp:slice_kinds_def intra_path_def)
  next
    case (Suc x)
    note IH = `\<And>m. \<lbrakk>distance m m' x; obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}\<rbrakk>
      \<Longrightarrow> \<exists>as'. m -as'\<rightarrow>\<^isub>\<iota>* m' \<and> preds (slice_kinds n\<^isub>c as') (cf # cfs) \<and>
               slice_edges n\<^isub>c cs as' = []`
    from `distance m m' (Suc x)` obtain a 
      where "valid_edge a" and "m = sourcenode a" and "intra_kind(kind a)"
      and "distance (targetnode a) m' x"
      and target:"targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
      distance (targetnode a') m' x \<and>
      valid_edge a' \<and> intra_kind(kind a') \<and> targetnode a' = nx)"
      by(auto elim:distance_successor_distance)
    have "m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
    proof
      assume "m \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      from `valid_edge a` `m = sourcenode a` have "valid_node m" by simp
      with `m \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` have "obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m}"
	by -(rule n_in_obs_intra)
      with `obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}` have "m = m'" by simp
      with `valid_node m` have "m -[]\<rightarrow>\<^isub>\<iota>* m'" 
	by(fastsimp intro:empty_path simp:intra_path_def)
      with `distance m m' (Suc x)` show False
	by(fastsimp elim:distance.cases)
    qed
    from `distance (targetnode a) m' x` `m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    obtain mx where "mx \<in> obs_intra (targetnode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastsimp elim:distance.cases path_ex_obs_intra)
    from `valid_edge a` `intra_kind(kind a)` `m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a`
    have "obs_intra (targetnode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> \<subseteq> 
      obs_intra (sourcenode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      by -(rule edge_obs_intra_subset,auto)
    with `mx \<in> obs_intra (targetnode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a`
      `obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}`
    have "m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" by auto
    hence "obs_intra (targetnode a) \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}" 
      by(rule obs_intra_singleton_element)
    from IH[OF `distance (targetnode a) m' x` this]
    obtain as where "targetnode a -as\<rightarrow>\<^isub>\<iota>* m'" and "preds (slice_kinds n\<^isub>c as) (cf#cfs)"
      and "slice_edges n\<^isub>c cs as = []" by blast
    from `targetnode a -as\<rightarrow>\<^isub>\<iota>* m'` `valid_edge a` `intra_kind(kind a)` 
      `m = sourcenode a`
    have "m -a#as\<rightarrow>\<^isub>\<iota>* m'" by(fastsimp intro:Cons_path simp:intra_path_def)
    from `\<forall>c \<in> set cs. sourcenode c \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
      `m = sourcenode a` `intra_kind(kind a)`
    have "\<not> slice_edge n\<^isub>c cs a" by(fastsimp simp:slice_edge_def intra_kind_def)
    with `slice_edges n\<^isub>c cs as = []` `intra_kind(kind a)` 
    have "slice_edges n\<^isub>c cs (a#as) = []" by(fastsimp simp:intra_kind_def)
    from `intra_kind(kind a)`
    show ?case
    proof(cases "kind a")
      case (UpdateEdge f)
      with `m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` have "slice_kind n\<^isub>c a = \<Up>id"
	by(fastsimp intro:slice_kind_Upd)
      hence "transfer (slice_kind n\<^isub>c a) (cf#cfs) = (cf#cfs)" 
	and "pred (slice_kind n\<^isub>c a) (cf#cfs)" by simp_all
      with `preds (slice_kinds n\<^isub>c as) (cf#cfs)` 
      have "preds (slice_kinds n\<^isub>c (a#as)) (cf#cfs)"
	by(simp add:slice_kinds_def)
      with `m -a#as\<rightarrow>\<^isub>\<iota>* m'` `slice_edges n\<^isub>c cs (a#as) = []` show ?thesis
	by blast
    next
      case (PredicateEdge Q)
      with `m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>` `m = sourcenode a` `distance m m' (Suc x)`  
	`obs_intra m \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub> = {m'}` `distance (targetnode a) m' x`
	target
      have "slice_kind n\<^isub>c a = (\<lambda>s. True)\<^isub>\<surd>"
	by(fastsimp intro:slice_kind_Pred_obs_nearer_SOME)
      hence "transfer (slice_kind n\<^isub>c a) (cf#cfs) = (cf#cfs)" 
	and "pred (slice_kind n\<^isub>c a) (cf#cfs)" by simp_all
      with `preds (slice_kinds n\<^isub>c as) (cf#cfs)` 
      have "preds (slice_kinds n\<^isub>c (a#as)) (cf#cfs)"
	by(simp add:slice_kinds_def)
      with `m -a#as\<rightarrow>\<^isub>\<iota>* m'` `slice_edges n\<^isub>c cs (a#as) = []` show ?thesis by blast
    qed (auto simp:intra_kind_def)
  qed
qed


lemma slp_to_intra_path_with_slice_edges:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'" and "slice_edges n\<^isub>c cs as = []"
  obtains as' where "n -as'\<rightarrow>\<^isub>\<iota>* n'" and "slice_edges n\<^isub>c cs as' = []"
proof(atomize_elim)
  from `n -as\<rightarrow>\<^bsub>sl\<^esub>* n'` have "n -as\<rightarrow>* n'" and "same_level_path as"
    by(simp_all add:slp_def)
  from `same_level_path as` have "same_level_path_aux [] as" and "upd_cs [] as = []"
    by(simp_all add:same_level_path_def)
  from `n -as\<rightarrow>* n'` `same_level_path_aux [] as` `upd_cs [] as = []` 
    `slice_edges n\<^isub>c cs as = []`
  show "\<exists>as'. n -as'\<rightarrow>\<^isub>\<iota>* n' \<and> slice_edges n\<^isub>c cs as' = []"
  proof(induct as arbitrary:n cs rule:length_induct)
    fix as n cs
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n''. n'' -as''\<rightarrow>* n' \<longrightarrow> same_level_path_aux [] as'' \<longrightarrow>
           upd_cs [] as'' = [] \<longrightarrow> (\<forall>cs'. slice_edges n\<^isub>c cs' as'' = [] \<longrightarrow>
           (\<exists>as'. n'' -as'\<rightarrow>\<^isub>\<iota>* n' \<and> slice_edges n\<^isub>c cs' as' = [])))"
      and "n -as\<rightarrow>* n'" and "same_level_path_aux [] as" and "upd_cs [] as = []"
      and "slice_edges n\<^isub>c cs as = []"
    show "\<exists>as'. n -as'\<rightarrow>\<^isub>\<iota>* n' \<and> slice_edges n\<^isub>c cs as' = []"
    proof(cases as)
      case Nil
      with `n -as\<rightarrow>* n'` show ?thesis by(fastsimp simp:intra_path_def)
    next
      case (Cons a' as')
      with `n -as\<rightarrow>* n'` Cons have "n = sourcenode a'" and "valid_edge a'" 
	and "targetnode a' -as'\<rightarrow>* n'"
	by(auto intro:path_split_Cons)
      show ?thesis
      proof(cases "kind a'" rule:edge_kind_cases)
	case Intra
	with Cons `same_level_path_aux [] as` have "same_level_path_aux [] as'"
	  by(fastsimp simp:intra_kind_def)
	moreover
	from Intra Cons `upd_cs [] as = []` have "upd_cs [] as' = []"
	  by(fastsimp simp:intra_kind_def)
	moreover
	from `slice_edges n\<^isub>c cs as = []` Cons Intra
	have "slice_edges n\<^isub>c cs as' = []" and "\<not> slice_edge n\<^isub>c cs a'"
	  by(cases "slice_edge n\<^isub>c cs a'",auto simp:intra_kind_def)+
	ultimately obtain as'' where "targetnode a' -as''\<rightarrow>\<^isub>\<iota>* n'"
	  and "slice_edges n\<^isub>c cs as'' = []"
	  using IH Cons `targetnode a' -as'\<rightarrow>* n'`
	  by(erule_tac x="as'" in allE) auto
	from `n = sourcenode a'` `valid_edge a'` Intra `targetnode a' -as''\<rightarrow>\<^isub>\<iota>* n'`
	have "n -a'#as''\<rightarrow>\<^isub>\<iota>* n'" by(fastsimp intro:Cons_path simp:intra_path_def)
	moreover
	from `slice_edges n\<^isub>c cs as'' = []` `\<not> slice_edge n\<^isub>c cs a'` Intra
	have "slice_edges n\<^isub>c cs (a'#as'') = []" by(auto simp:intra_kind_def)
	ultimately show ?thesis by blast
      next
	case (Call Q r p f)
	with Cons `same_level_path_aux [] as`
	have "same_level_path_aux [a'] as'" by simp
	from Call Cons `upd_cs [] as = []` have "upd_cs [a'] as' = []"
	  by simp
	hence "as' \<noteq> []" by fastsimp
	with `upd_cs [a'] as' = []` obtain xs ys where "as' = xs@ys" and "xs \<noteq> []"
	and "upd_cs [a'] xs = []" and "upd_cs [] ys = []"
	and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []"
	  by -(erule upd_cs_empty_split,auto)
	from `same_level_path_aux [a'] as'` `as' = xs@ys` `upd_cs [a'] xs = []`
	have "same_level_path_aux [a'] xs"  and "same_level_path_aux [] ys"
	  by(rule slpa_split)+
	with `upd_cs [a'] xs = []` have "upd_cs ([a']@cs) xs = []@cs"
	  by(fastsimp intro:same_level_path_upd_cs_callstack_Append)
	from `slice_edges n\<^isub>c cs as = []` Cons Call
	have "slice_edges n\<^isub>c (a'#cs) as' = []" and "\<not> slice_edge n\<^isub>c cs a'"
	  by(cases "slice_edge n\<^isub>c cs a'",auto)+
	from `slice_edges n\<^isub>c (a'#cs) as' = []` `as' = xs@ys` 
	  `upd_cs ([a']@cs) xs = []@cs`
	have "slice_edges n\<^isub>c cs ys = []" 
	  by(fastsimp dest:slice_edges_Nil_split)
	from `same_level_path_aux [a'] xs` `upd_cs [a'] xs = []`
	  `\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []`
	have "last xs \<in> get_return_edges (last [a'])"
	  by(fastsimp intro!:slpa_get_return_edges)
	with `valid_edge a'` Call
	obtain a where "valid_edge a" and "sourcenode a = sourcenode a'"
	  and "targetnode a = targetnode (last xs)" and "kind a = (\<lambda>cf. False)\<^isub>\<surd>"
	  by -(drule call_return_node_edge,auto)
	from `targetnode a = targetnode (last xs)` `xs \<noteq> []`
	have "targetnode a = targetnode (last (a'#xs))" by simp
	from `as' = xs@ys` `xs \<noteq> []` Cons have "length ys < length as" by simp
	from `targetnode a' -as'\<rightarrow>* n'` `as' = xs@ys` `xs \<noteq> []`
	have "targetnode (last (a'#xs)) -ys\<rightarrow>* n'"
	  by(cases xs rule:rev_cases,auto dest:path_split)
	with IH `length ys < length as` `same_level_path_aux [] ys`
	  `upd_cs [] ys = []` `slice_edges n\<^isub>c cs ys = []`
	obtain as'' where "targetnode (last (a'#xs)) -as''\<rightarrow>\<^isub>\<iota>* n'"
	  and "slice_edges n\<^isub>c cs as'' = []"
	  apply(erule_tac x="ys" in allE) apply clarsimp
	  apply(erule_tac x="targetnode (last (a'#xs))" in allE) 
	  apply clarsimp apply(erule_tac x="cs" in allE)
	  by clarsimp
	from `sourcenode a = sourcenode a'` `n = sourcenode a'`
	  `targetnode a = targetnode (last (a'#xs))` `valid_edge a`
	  `kind a = (\<lambda>cf. False)\<^isub>\<surd>` `targetnode (last (a'#xs)) -as''\<rightarrow>\<^isub>\<iota>* n'`
	have "n -a#as''\<rightarrow>\<^isub>\<iota>* n'"
	  by(fastsimp intro:Cons_path simp:intra_path_def intra_kind_def)
	moreover
	from `kind a = (\<lambda>cf. False)\<^isub>\<surd>` `slice_edges n\<^isub>c cs as'' = []`
	  `\<not> slice_edge n\<^isub>c cs a'` `sourcenode a = sourcenode a'`
	have "slice_edges n\<^isub>c cs (a#as'') = []" 
	  by(cases "kind a'")(auto simp:slice_edge_def)
	ultimately show ?thesis by blast
      next
	case (Return Q p f)
	with Cons `same_level_path_aux [] as` have False by simp
	thus ?thesis by simp
      qed
    qed
  qed
qed


subsection {* @{text "n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow>* (ms',s')"} : the reflexive transitive 
  closure of @{text "n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')"} *}


inductive trans_observable_moves :: 
  "'node SDG_node \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
   (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge list \<Rightarrow> 'node list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') =_\<Rightarrow>* '(_,_')" [51,50,0,0,50,0,0] 51) 

where tom_Nil:
  "length ms = length s \<Longrightarrow> n\<^isub>c,f \<turnstile> (ms,s) =[]\<Rightarrow>* (ms,s)"

| tom_Cons:
  "\<lbrakk>n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s'); n\<^isub>c,f \<turnstile> (ms',s') =as'\<Rightarrow>* (ms'',s'')\<rbrakk>
  \<Longrightarrow> n\<^isub>c,f \<turnstile> (ms,s) =(last as)#as'\<Rightarrow>* (ms'',s'')"


lemma tom_split_snoc:
  assumes "n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow>* (ms',s')" and "as \<noteq> []"
  obtains asx asx' ms'' s'' where "as = asx@[last asx']" 
  and "n\<^isub>c,f \<turnstile> (ms,s) =asx\<Rightarrow>* (ms'',s'')" and "n\<^isub>c,f \<turnstile> (ms'',s'') =asx'\<Rightarrow> (ms',s')"
proof(atomize_elim)
  from assms show "\<exists>asx asx' ms'' s''. as = asx @ [last asx'] \<and>
    n\<^isub>c,f \<turnstile> (ms,s) =asx\<Rightarrow>* (ms'',s'') \<and> n\<^isub>c,f \<turnstile> (ms'',s'') =asx'\<Rightarrow> (ms',s')"
  proof(induct rule:trans_observable_moves.induct)
    case (tom_Cons n\<^isub>c f ms s as ms' s' as' ms'' s'')
    note IH = `as' \<noteq> [] \<Longrightarrow> \<exists>asx asx' msx sx. as' = asx @ [last asx'] \<and>
      n\<^isub>c,f \<turnstile> (ms',s') =asx\<Rightarrow>* (msx,sx) \<and> n\<^isub>c,f \<turnstile> (msx,sx) =asx'\<Rightarrow> (ms'',s'')`
    show ?case
    proof(cases "as' = []")
      case True
      with `n\<^isub>c,f \<turnstile> (ms',s') =as'\<Rightarrow>* (ms'',s'')` have [simp]:"ms'' = ms'" "s'' = s'"
	by(auto elim:trans_observable_moves.cases)
      from `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')` have "length ms = length s"
	by(rule observable_moves_equal_length)
      hence "n\<^isub>c,f \<turnstile> (ms,s) =[]\<Rightarrow>* (ms,s)" by(rule tom_Nil)
      with `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')` True show ?thesis by fastsimp
    next
      case False
      from IH[OF this] obtain xs xs' msx sx where "as' = xs @ [last xs']"
	and "n\<^isub>c,f \<turnstile> (ms',s') =xs\<Rightarrow>* (msx,sx)" 
	and "n\<^isub>c,f \<turnstile> (msx,sx) =xs'\<Rightarrow> (ms'',s'')" by blast
      from `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')` `n\<^isub>c,f \<turnstile> (ms',s') =xs\<Rightarrow>* (msx,sx)`
      have "n\<^isub>c,f \<turnstile> (ms,s) =(last as)#xs\<Rightarrow>* (msx,sx)"
	by(rule trans_observable_moves.tom_Cons)
      with `n\<^isub>c,f \<turnstile> (msx,sx) =xs'\<Rightarrow> (ms'',s'')` `as' = xs @ [last xs']`
      show ?thesis by fastsimp
    qed
  qed simp
qed


lemma tom_preserves_stacks:
  assumes "n\<^isub>c,f \<turnstile> (m#ms,s) =as\<Rightarrow>* (m'#ms',s')" and "valid_node m" 
  and "valid_call_list cs m" and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" 
  and "valid_return_list rs m" and "length rs = length cs" and "ms = targetnodes rs"
  obtains cs' rs' where "valid_node m'" and "valid_call_list cs' m'"
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'"
proof(atomize_elim)
  from assms show "\<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and> valid_return_list rs' m' \<and>
    length rs' = length cs' \<and> ms' = targetnodes rs'"
  proof(induct n\<^isub>c f msx\<equiv>"m#ms" s as msx'\<equiv>"m'#ms'" s' arbitrary:m ms cs rs
      rule:trans_observable_moves.induct)
    case (tom_Nil msx sx n\<^isub>c f m ms)
    thus ?case
      apply(rule_tac x="cs" in exI)
      apply(rule_tac x="rs" in exI)
      by clarsimp
  next
    case (tom_Cons n\<^isub>c f msx sx as msx' sx' as' msx'' sx'' m ms)
    note IH = `\<And>m ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); valid_return_list rs m;
      length rs = length cs; ms = targetnodes rs; msx' = m # ms; msx'' = m' # ms'\<rbrakk>
      \<Longrightarrow> \<exists>cs' rs'. valid_node m' \<and> valid_call_list cs' m' \<and>
      (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
      valid_return_list rs' m' \<and> length rs' = length cs' \<and>
      ms' = targetnodes rs'`
    from `n\<^isub>c,f \<turnstile> (msx,sx) =as\<Rightarrow> (msx',sx')`
    obtain m'' ms'' where "msx' = m''#ms''"
      apply(cases msx') apply(auto elim!:observable_moves.cases observable_move.cases)
      by(case_tac "msa") auto
    with `n\<^isub>c,f \<turnstile> (msx,sx) =as\<Rightarrow> (msx',sx')` `msx = m # ms` `valid_node m`
      `valid_call_list cs m` `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
      `valid_return_list rs m` `length rs = length cs` `ms = targetnodes rs`
    obtain cs'' rs'' where "valid_node m''" and "valid_call_list cs'' m''"
      and "\<forall>i < length rs''. rs''!i \<in> get_return_edges (cs''!i)"
      and "valid_return_list rs'' m''" and "length rs'' = length cs''" 
      and "ms'' = targetnodes rs''"
      by(auto elim!:observable_moves_preserves_stack)
    from IH[OF this(1-6) `msx' = m''#ms''` `msx'' = m' # ms'`]
    show ?case by fastsimp
  qed
qed




lemma vpa_trans_observable_moves:
  assumes "valid_path_aux cs as" and "m -as\<rightarrow>* m'" and "preds (kinds as) s" 
  and "transfers (kinds as) s = s'" and "valid_call_list cs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)"
  and "valid_return_list rs m" 
  and "length rs = length cs" and "length s = Suc (length cs)" 
  obtains ms ms'' s'' ms' as' as''
  where "n\<^isub>c,kind \<turnstile> (m#ms,s) =slice_edges n\<^isub>c cs as\<Rightarrow>* (ms'',s'')"
  and "n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')" 
  and "ms = targetnodes rs" and "length ms = length cs"
  and "\<forall>i<length cs. call_of_return_node (ms!i) (sourcenode (cs!i))"
  and "slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as''" 
  and "m -as''@as'\<rightarrow>* m'" and "valid_path_aux cs (as''@as')"
proof(atomize_elim)
  from assms show "\<exists>ms ms'' s'' as' ms' as''.
    n\<^isub>c,kind \<turnstile> (m # ms,s) =slice_edges n\<^isub>c cs as\<Rightarrow>* (ms'',s'') \<and>
    n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s') \<and> 
    ms = targetnodes rs \<and> length ms = length cs \<and>
    (\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))) \<and>
    slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as'' \<and>
    m -as'' @ as'\<rightarrow>* m' \<and> valid_path_aux cs (as'' @ as')"
  proof(induct arbitrary:m s rs rule:vpa_induct)
    case (vpa_empty cs)
    from `m -[]\<rightarrow>* m'` have [simp]:"m' = m" by fastsimp
    from `transfers (kinds []) s = s'` `length s = Suc (length cs)` 
    have [simp]:"s' = s" by(cases cs)(auto simp:kinds_def)
    from `valid_call_list cs m` `valid_return_list rs m`
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `length rs = length cs`
    have "\<forall>i<length cs. call_of_return_node (targetnodes rs!i) (sourcenode (cs!i))"
      by(rule get_return_edges_call_of_return_nodes)
    with `length s = Suc (length cs)` `m -[]\<rightarrow>* m'` `length rs = length cs` show ?case
      apply(rule_tac x="targetnodes rs" in exI)
      apply(rule_tac x="m#targetnodes rs" in exI)
      apply(rule_tac x="s" in exI)
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="targetnodes rs" in exI)
      apply(rule_tac x="[]" in exI)
      by(fastsimp intro:tom_Nil silent_moves_Nil simp:targetnodes_def)
  next
    case (vpa_intra cs a as)
    note IH = `\<And>m s rs. \<lbrakk>m -as\<rightarrow>* m'; preds (kinds as) s; transfers (kinds as) s = s';
      valid_call_list cs m; \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i);
      valid_return_list rs m; length rs = length cs; length s = Suc (length cs)\<rbrakk>
      \<Longrightarrow> \<exists>ms ms'' s'' as' ms' as''.
      n\<^isub>c,kind \<turnstile> (m # ms,s) =slice_edges n\<^isub>c cs as\<Rightarrow>* (ms'',s'') \<and>
      n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s') \<and> ms = targetnodes rs \<and>
      length ms = length cs \<and>
      (\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))) \<and>
      slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as'' \<and>
      m -as'' @ as'\<rightarrow>* m' \<and> valid_path_aux cs (as'' @ as')`
    from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
      and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
    from `preds (kinds (a # as)) s` have "pred (kind a) s"
      and "preds (kinds as) (transfer (kind a) s)" by(auto simp:kinds_def)
    from `transfers (kinds (a # as)) s = s'`
    have "transfers (kinds as) (transfer (kind a) s) = s'" by(fastsimp simp:kinds_def)
    from `valid_edge a` `intra_kind (kind a)`
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    from `valid_call_list cs m` `m = sourcenode a`
      `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_call_list cs (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    from `intra_kind (kind a)` `length s = Suc (length cs)`
    have "length (transfer (kind a) s) = Suc (length cs)"
      by(cases s)(auto simp:intra_kind_def)
   from `valid_return_list rs m` `m = sourcenode a` 
     `get_proc (sourcenode a) = get_proc (targetnode a)`
    have "valid_return_list rs (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="cs'" in allE) apply clarsimp
      by(case_tac cs') auto
    from IH[OF `targetnode a -as\<rightarrow>* m'` `preds (kinds as) (transfer (kind a) s)`
      `transfers (kinds as) (transfer (kind a) s) = s'` 
      `valid_call_list cs (targetnode a)` 
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` this `length rs = length cs`
      `length (transfer (kind a) s) = Suc (length cs)`]
    obtain ms ms'' s'' as' ms' as'' where "length ms = length cs"
      and "n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) =slice_edges n\<^isub>c cs as\<Rightarrow>*
                       (ms'',s'')" 
      and paths:"n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
      "ms = targetnodes rs"
      "\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))"
      "slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as''"
      "targetnode a -as'' @ as'\<rightarrow>* m'" "valid_path_aux cs (as'' @ as')"
      by blast
    from `\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))`
      `length ms = length cs`
    have "\<forall>mx \<in> set ms. return_node mx"
      by(auto simp:call_of_return_node_def in_set_conv_nth)
    show ?case
    proof(cases "(\<forall>m \<in> set ms. \<exists>m'. call_of_return_node m m' \<and> 
	m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<and> m \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with `m = sourcenode a` `length ms = length cs` `intra_kind (kind a)`
	`\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))`
      have "slice_edge n\<^isub>c cs a"
	by(fastsimp simp:slice_edge_def in_set_conv_nth intra_kind_def)
      with `intra_kind (kind a)`
      have "slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs as"
	by(fastsimp simp:intra_kind_def)
      from True `pred (kind a) s` `valid_edge a` `intra_kind (kind a)`
	`\<forall>mx \<in> set ms. return_node mx` `length ms = length cs` `m = sourcenode a`
	`length s = Suc (length cs)` `length (transfer (kind a) s) = Suc (length cs)`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) -a\<rightarrow> (targetnode a#ms,transfer (kind a) s)"
	by(fastsimp intro!:observable_move_intra)
      with `length ms = length cs` `length s = Suc (length cs)`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =[]@[a]\<Rightarrow> 
	              (targetnode a#ms,transfer (kind a) s)"
	by(fastsimp intro:observable_moves_snoc silent_moves_Nil)
      with `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) =slice_edges n\<^isub>c cs as\<Rightarrow>*
        (ms'',s'')`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =last [a]#slice_edges n\<^isub>c cs as\<Rightarrow>* (ms'',s'')"
	by(fastsimp intro:tom_Cons)
      with `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs as`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>* (ms'',s'')"
	by simp
      moreover
      from `slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as''` `slice_edge n\<^isub>c cs a`
	`intra_kind (kind a)`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs (a#as'')"
	by(fastsimp simp:intra_kind_def)
      ultimately show ?thesis 
	using paths `m = sourcenode a` `valid_edge a` `intra_kind (kind a)`
	`length ms = length cs` `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs as`
	apply(rule_tac x="ms" in exI)
	apply(rule_tac x="ms''" in exI)
	apply(rule_tac x="s''" in exI)
	apply(rule_tac x="as'" in exI)
	apply(rule_tac x="ms'" in exI)
	apply(rule_tac x="a#as''" in exI)
	by(auto intro:Cons_path simp:intra_kind_def)
    next
      case False
      with `\<forall>mx \<in> set ms. return_node mx`
      have disj:"(\<exists>m \<in> set ms. \<exists>m'. call_of_return_node m m' \<and> 
	m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<or> m \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
	by(fastsimp dest:return_node_call_of_return_node)
      with `m = sourcenode a` `length ms = length cs` `intra_kind (kind a)`
	`\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))`
      have "\<not> slice_edge n\<^isub>c cs a" 
	by(fastsimp simp:slice_edge_def in_set_conv_nth intra_kind_def)
      with `intra_kind (kind a)`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs as"
	by(fastsimp simp:intra_kind_def)
      from disj `pred (kind a) s` `valid_edge a` `intra_kind (kind a)`
	`\<forall>mx \<in> set ms. return_node mx` `length ms = length cs` `m = sourcenode a`
	`length s = Suc (length cs)` `length (transfer (kind a) s) = Suc (length cs)`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) -a\<rightarrow>\<^isub>\<tau> (targetnode a#ms,transfer (kind a) s)"
	by(fastsimp intro!:silent_move_intra)
      from `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) =slice_edges n\<^isub>c cs as\<Rightarrow>*
                      (ms'',s'')`
      show ?thesis
      proof(rule trans_observable_moves.cases)
	fix msx sx n\<^isub>c' f
	assume "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" and "slice_edges n\<^isub>c cs as = []"
	  and [simp]:"ms'' = msx" "s'' = sx" and "length msx = length sx"
	from `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs as` 
	  `slice_edges n\<^isub>c cs as = []`
	have "slice_edges n\<^isub>c cs (a#as) = []" by simp 
	with `length ms = length cs` `length s = Suc (length cs)`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>*
	                (sourcenode a#ms,s)"
	  by(fastsimp intro:tom_Nil)
	moreover
	from `n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `targetnode a # ms = msx`
	  `transfer (kind a) s = sx` `ms'' = msx` `s'' = sx`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) -a\<rightarrow>\<^isub>\<tau> (targetnode a#ms,transfer (kind a) s)`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	  by(fastsimp intro:silent_moves_Cons)
	from this `valid_edge a` `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
	  `ms = targetnodes rs` `valid_return_list rs m` `length rs = length cs`
	  `length s = Suc (length cs)` `m = sourcenode a`
	have "sourcenode a -a#as'\<rightarrow>* m'" and "valid_path_aux cs (a#as')"
	  by -(rule silent_moves_vpa_path,(fastsimp simp:targetnodes_def)+)+
	ultimately show ?thesis using `m = sourcenode a` `length ms = length cs`
	  `\<forall>i<length cs. call_of_return_node (ms ! i) (sourcenode (cs ! i))`
	  `slice_edges n\<^isub>c cs (a#as) = []` `intra_kind (kind a)`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
	  `ms = targetnodes rs`
	  apply(rule_tac x="ms" in exI)
	  apply(rule_tac x="sourcenode a#ms" in exI)
	  apply(rule_tac x="s" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="[]" in exI)
	  by(auto simp:intra_kind_def)
      next
	fix n\<^isub>c' f msx sx asx msx' sx' asx' msx'' sx''
	assume [simp]:"n\<^isub>c = n\<^isub>c'" and "kind = f" and "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" and "slice_edges n\<^isub>c cs as = last asx # asx'"
	  and "ms'' = msx''" and "s'' = sx''" 
	  and "n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')"
	  and "n\<^isub>c',f \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')"
	from `kind = f` have [simp]:"f = kind" by simp
	from `n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) -a\<rightarrow>\<^isub>\<tau> 
	  (targetnode a#ms,transfer (kind a) s)` `n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')`
	  `transfer (kind a) s = sx` `targetnode a # ms = msx`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =a#asx\<Rightarrow> (msx',sx')"
	  by(fastsimp intro:silent_move_observable_moves)
	with `n\<^isub>c',f \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')` `ms'' = msx''` `s'' = sx''`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#ms,s) =last (a#asx)#asx'\<Rightarrow>* (ms'',s'')"
	  by(fastsimp intro:trans_observable_moves.tom_Cons)
	moreover
	from `n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')` have "asx \<noteq> []"
	  by(fastsimp elim:observable_moves.cases)
	with `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs as`
	  `slice_edges n\<^isub>c cs as = last asx # asx'`
	have "slice_edges n\<^isub>c cs (a#as) = last (a#asx)#asx'" by simp
	moreover
	from `\<not> slice_edge n\<^isub>c cs a` `slice_edges n\<^isub>c cs as = slice_edges n\<^isub>c cs as''`
	  `intra_kind (kind a)`
	have "slice_edges n\<^isub>c cs (a # as) = slice_edges n\<^isub>c cs (a # as'')"
	  by(fastsimp simp:intra_kind_def)
	ultimately show ?thesis using paths `m = sourcenode a` `intra_kind (kind a)`
	  `length ms = length cs` `ms = targetnodes rs` `valid_edge a`
	  apply(rule_tac x="ms" in exI)
	  apply(rule_tac x="ms''" in exI)
	  apply(rule_tac x="s''" in exI)
	  apply(rule_tac x="as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="a#as''" in exI)
	  by(auto intro:Cons_path simp:intra_kind_def)
      qed
    qed
  next
    case (vpa_Call cs a as Q r p fs)
    note IH = `\<And>m s rs. \<lbrakk>m -as\<rightarrow>* m'; preds (kinds as) s; transfers (kinds as) s = s';
      valid_call_list (a # cs) m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges ((a # cs) ! i);
      valid_return_list rs m; length rs = length (a # cs);
      length s = Suc (length (a # cs))\<rbrakk>
      \<Longrightarrow> \<exists>ms ms'' s'' as' ms' as''.
      n\<^isub>c,kind \<turnstile> (m # ms,s) =slice_edges n\<^isub>c (a # cs) as\<Rightarrow>* (ms'',s'') \<and>
      n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s') \<and> ms = targetnodes rs \<and>
      length ms = length (a # cs) \<and>
      (\<forall>i<length (a # cs). call_of_return_node (ms ! i) (sourcenode ((a # cs) ! i))) \<and>
      slice_edges n\<^isub>c (a # cs) as = slice_edges n\<^isub>c (a # cs) as'' \<and>
      m -as'' @ as'\<rightarrow>* m' \<and> valid_path_aux (a # cs) (as'' @ as')`
    from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
      and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
    from `preds (kinds (a # as)) s` have "pred (kind a) s"
      and "preds (kinds as) (transfer (kind a) s)" by(auto simp:kinds_def)
    from `transfers (kinds (a # as)) s = s'`
    have "transfers (kinds as) (transfer (kind a) s) = s'" by(fastsimp simp:kinds_def)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
      by(rule get_proc_call)
    with `valid_call_list cs m` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `m = sourcenode a`
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain a' where "a' \<in> get_return_edges a"
      by(fastsimp dest:get_return_edge_call)
    with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain Q' f' where "kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'"
      by(fastsimp dest!:call_return_edges)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'` have "get_proc (sourcenode a') = p"
      by(rule get_proc_return)
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `a' \<in> get_return_edges a`
    have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
      by auto(case_tac i,auto)
    from `valid_edge a` `a' \<in> get_return_edges a`
    have "get_proc (sourcenode a) = get_proc (targetnode a')" 
      by(rule get_proc_get_return_edge)
    with `valid_return_list rs m` `valid_edge a'` `kind a' = Q'\<^bsub>p\<^esub>\<hookleftarrow>f'`
      `get_proc (sourcenode a') = p` `get_proc (targetnode a) = p` `m = sourcenode a`
    have "valid_return_list (a'#rs) (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:targetnodes_def)
    from `length rs = length cs` have "length (a'#rs) = length (a#cs)" by simp
    from `length s = Suc (length cs)` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    have "length (transfer (kind a) s) = Suc (length (a#cs))"
      by(cases s) auto
    from IH[OF `targetnode a -as\<rightarrow>* m'` `preds (kinds as) (transfer (kind a) s)`
      `transfers (kinds as) (transfer (kind a) s) = s'` 
      `valid_call_list (a # cs) (targetnode a)` 
      `\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)`
      `valid_return_list (a'#rs) (targetnode a)` `length (a'#rs) = length (a#cs)`
      `length (transfer (kind a) s) = Suc (length (a#cs))`]
    obtain ms ms'' s'' as' ms' as'' where "length ms = length (a#cs)"
      and "n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
                     =slice_edges n\<^isub>c (a#cs) as\<Rightarrow>* (ms'',s'')" 
      and paths:"n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
      "ms = targetnodes (a'#rs)"
      "\<forall>i<length (a#cs). call_of_return_node (ms ! i) (sourcenode ((a#cs) ! i))"
      "slice_edges n\<^isub>c (a#cs) as = slice_edges n\<^isub>c (a#cs) as''"
      "targetnode a -as'' @ as'\<rightarrow>* m'" "valid_path_aux (a#cs) (as'' @ as')"
      by blast
    from `ms = targetnodes (a'#rs)` obtain x xs where [simp]:"ms = x#xs"
      and "x = targetnode a'" and "xs = targetnodes rs"
      by(cases ms)(auto simp:targetnodes_def)
    from `\<forall>i<length (a#cs). call_of_return_node (ms ! i) (sourcenode ((a#cs) ! i))`
      `length ms = length (a#cs)`
    have "\<forall>mx \<in> set xs. return_node mx"
      apply(auto simp:in_set_conv_nth) apply(case_tac i)
      apply(erule_tac x="Suc 0" in allE)
      by(auto simp:call_of_return_node_def)
    show ?case
    proof(cases "(\<forall>m \<in> set xs. \<exists>m'. call_of_return_node m m' \<and> 
	m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<and> sourcenode a \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with `\<forall>i<length (a#cs). call_of_return_node (ms ! i) (sourcenode ((a#cs) ! i))`
	`length ms = length (a#cs)` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "slice_edge n\<^isub>c cs a"
	apply(auto simp:slice_edge_def in_set_conv_nth)
	by(erule_tac x="Suc i" in allE) auto
      with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c (a#cs) as" by simp
      from True `pred (kind a) s` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	`valid_edge a'` `a' \<in> get_return_edges a`
	`\<forall>mx \<in> set xs. return_node mx` `length ms = length (a#cs)` `m = sourcenode a`
	`length s = Suc (length cs)` 
	`length (transfer (kind a) s) = Suc (length (a#cs))`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) -a\<rightarrow> 
	(targetnode a#targetnode a'#xs,transfer (kind a) s)"
	by -(rule_tac a'="a'" in observable_move_call,fastsimp+)
      with `length ms = length (a#cs)` `length s = Suc (length cs)`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =[]@[a]\<Rightarrow> 
	(targetnode a#targetnode a'#xs,transfer (kind a) s)"
	by(fastsimp intro:observable_moves_snoc silent_moves_Nil)
      with `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
	=slice_edges n\<^isub>c (a#cs) as\<Rightarrow>* (ms'',s'')` `x = targetnode a'`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =last [a]#slice_edges n\<^isub>c (a#cs) as\<Rightarrow>* 
	(ms'',s'')"
	by -(rule tom_Cons,auto)
      with `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c (a#cs) as`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>* (ms'',s'')"
	by simp
      moreover
      from `slice_edges n\<^isub>c (a#cs) as = slice_edges n\<^isub>c (a#cs) as''`
	`slice_edge n\<^isub>c cs a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs (a#as'')" by simp
      ultimately show ?thesis
	using paths `m = sourcenode a` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	  `length ms = length (a#cs)` `xs = targetnodes rs`
	  `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c (a#cs) as`
	apply(rule_tac x="xs" in exI)
	apply(rule_tac x="ms''" in exI)
	apply(rule_tac x="s''" in exI)
	apply(rule_tac x="as'" in exI)
	apply(rule_tac x="ms'" in exI)
	apply(rule_tac x="a#as''" in exI)
	by(auto intro:Cons_path simp:targetnodes_def)
    next
      case False
      with `\<forall>mx \<in> set xs. return_node mx`
      have disj:"(\<exists>m \<in> set xs. \<exists>m'. call_of_return_node m m' \<and> 
	m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>) \<or> sourcenode a \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
	by(fastsimp dest:return_node_call_of_return_node)
      with `\<forall>i<length (a#cs). call_of_return_node (ms ! i) (sourcenode ((a#cs) ! i))`
	`length ms = length (a#cs)` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "\<not> slice_edge n\<^isub>c cs a"
	apply(auto simp:slice_edge_def in_set_conv_nth)
	by(erule_tac x="Suc i" in allE) auto
      with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c (a#cs) as" by simp
      from disj `pred (kind a) s` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	`valid_edge a'` `a' \<in> get_return_edges a`
	`\<forall>mx \<in> set xs. return_node mx` `length ms = length (a#cs)` `m = sourcenode a`
	`length s = Suc (length cs)` 
	`length (transfer (kind a) s) = Suc (length (a#cs))`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) -a\<rightarrow>\<^isub>\<tau>
	(targetnode a#targetnode a'#xs,transfer (kind a) s)"
	by -(rule_tac a'="a'" in silent_move_call,fastsimp+)
      from `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
	=slice_edges n\<^isub>c (a#cs) as\<Rightarrow>* (ms'',s'')`
      show ?thesis
      proof(rule trans_observable_moves.cases)
	fix msx sx n\<^isub>c' f
	assume "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" and "slice_edges n\<^isub>c (a#cs) as = []"
	  and [simp]:"ms'' = msx" "s'' = sx" and "length msx = length sx"
	from `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c (a#cs) as` 
	  `slice_edges n\<^isub>c (a#cs) as = []`
	have "slice_edges n\<^isub>c cs (a#as) = []" by simp
	with `length ms = length (a#cs)` `length s = Suc (length cs)`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>*
	                (sourcenode a#xs,s)"
	  by(fastsimp intro:tom_Nil)
	moreover
	from `n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `targetnode a # ms = msx`
	  `transfer (kind a) s = sx` `ms'' = msx` `s'' = sx` `x = targetnode a'`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) -a\<rightarrow>\<^isub>\<tau> 
	  (targetnode a#targetnode a'#xs,transfer (kind a) s)`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	  by(auto intro:silent_moves_Cons)
	from this `valid_edge a` 
	  `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
	  `xs = targetnodes rs` `valid_return_list rs m` `length rs = length cs`
	  `length s = Suc (length cs)` `m = sourcenode a`
	have "sourcenode a -a#as'\<rightarrow>* m'" and "valid_path_aux cs (a#as')"
	  by -(rule silent_moves_vpa_path,(fastsimp simp:targetnodes_def)+)+
	ultimately show ?thesis using `m = sourcenode a` `length ms = length (a#cs)`
	  `\<forall>i<length (a#cs). call_of_return_node (ms ! i) (sourcenode ((a#cs) ! i))`
	  `slice_edges n\<^isub>c cs (a#as) = []` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
	  `xs = targetnodes rs`
	  apply(rule_tac x="xs" in exI)
	  apply(rule_tac x="sourcenode a#xs" in exI)
	  apply(rule_tac x="s" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="[]" in exI)
	  by auto
      next
	fix n\<^isub>c' f msx sx asx msx' sx' asx' msx'' sx''
	assume [simp]:"n\<^isub>c = n\<^isub>c'" and "kind = f" and "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" 
	  and "slice_edges n\<^isub>c (a#cs) as = last asx # asx'"
	  and "ms'' = msx''" and "s'' = sx''" 
	  and "n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')"
	  and "n\<^isub>c',f \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')"
	from `kind = f` have [simp]:"f = kind" by simp
	from `n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) -a\<rightarrow>\<^isub>\<tau> 
	  (targetnode a#targetnode a'#xs,transfer (kind a) s)`
	  `n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')` `x = targetnode a'`
	  `transfer (kind a) s = sx` `targetnode a # ms = msx`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =a#asx\<Rightarrow> (msx',sx')"
	  by(auto intro:silent_move_observable_moves)
	with `n\<^isub>c',f \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')` `ms'' = msx''` `s'' = sx''`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#xs,s) =last (a#asx)#asx'\<Rightarrow>* (ms'',s'')"
	  by(fastsimp intro:trans_observable_moves.tom_Cons)
	moreover
	from `n\<^isub>c',f \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')` have "asx \<noteq> []"
	  by(fastsimp elim:observable_moves.cases)
	with `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c (a#cs) as`
	  `slice_edges n\<^isub>c (a#cs) as = last asx # asx'`
	have "slice_edges n\<^isub>c cs (a#as) = last (a#asx)#asx'" by simp
	moreover
	from `\<not> slice_edge n\<^isub>c cs a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	  `slice_edges n\<^isub>c (a#cs) as = slice_edges n\<^isub>c (a#cs) as''`
	have "slice_edges n\<^isub>c cs (a # as) = slice_edges n\<^isub>c cs (a # as'')" by simp
	ultimately show ?thesis using paths `m = sourcenode a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
	  `length ms = length (a#cs)` `xs = targetnodes rs` `valid_edge a`
	  apply(rule_tac x="xs" in exI)
	  apply(rule_tac x="ms''" in exI)
	  apply(rule_tac x="s''" in exI)
	  apply(rule_tac x="as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="a#as''" in exI)
	  by(auto intro:Cons_path simp:targetnodes_def)
      qed
    qed
  next
    case (vpa_ReturnEmpty cs a as Q p f)
    from `preds (kinds (a # as)) s` `length s = Suc (length cs)` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
      `cs = []`
    have False by(cases s)(auto simp:kinds_def)
    thus ?case by simp
  next
    case (vpa_ReturnCons cs a as Q p f c' cs')
    note IH = `\<And>m s rs. \<lbrakk>m -as\<rightarrow>* m'; preds (kinds as) s; transfers (kinds as) s = s';
      valid_call_list cs' m; \<forall>i<length rs. rs ! i \<in> get_return_edges (cs' ! i);
      valid_return_list rs m; length rs = length cs'; length s = Suc (length cs')\<rbrakk>
      \<Longrightarrow> \<exists>ms ms'' s'' as' ms' as''.
      n\<^isub>c,kind \<turnstile> (m # ms,s) =slice_edges n\<^isub>c cs' as\<Rightarrow>* (ms'',s'') \<and>
      n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s') \<and> ms = targetnodes rs \<and>
      length ms = length cs' \<and>
      (\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))) \<and>
      slice_edges n\<^isub>c cs' as = slice_edges n\<^isub>c cs' as'' \<and>
      m -as'' @ as'\<rightarrow>* m' \<and> valid_path_aux cs' (as'' @ as')`
    from `m -a # as\<rightarrow>* m'` have "m = sourcenode a" and "valid_edge a"
      and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
    from `preds (kinds (a # as)) s` have "pred (kind a) s"
      and "preds (kinds as) (transfer (kind a) s)" by(auto simp:kinds_def)
    from `transfers (kinds (a # as)) s = s'`
    have "transfers (kinds as) (transfer (kind a) s) = s'" by(fastsimp simp:kinds_def)
    from `valid_call_list cs m` `cs = c' # cs'` have "valid_edge c'"
      by(fastsimp simp:valid_call_list_def)
    from `valid_edge c'` `a \<in> get_return_edges c'`
    have "get_proc (sourcenode c') = get_proc (targetnode a)"
      by(rule get_proc_get_return_edge)
    from `valid_call_list cs m` `cs = c' # cs'`
      `get_proc (sourcenode c') = get_proc (targetnode a)`
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    from `length rs = length cs` `cs = c' # cs'` obtain r' rs' 
      where [simp]:"rs = r'#rs'" and "length rs' = length cs'" by(cases rs) auto
    from `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `cs = c' # cs'`
    have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      and "r' \<in> get_return_edges c'" by auto
    with `valid_edge c'` `a \<in> get_return_edges c'` have [simp]:"a = r'" 
      by -(rule get_return_edges_unique)
    with `valid_return_list rs m` 
    have "valid_return_list rs' (targetnode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="r' # cs'" in allE)
      by(case_tac cs')(auto simp:targetnodes_def)
    from `length s = Suc (length cs)` `cs = c' # cs'` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
    have "length (transfer (kind a) s) = Suc (length cs')"
      by(cases s)(auto,case_tac list,auto)
    from IH[OF `targetnode a -as\<rightarrow>* m'` `preds (kinds as) (transfer (kind a) s)`
      `transfers (kinds as) (transfer (kind a) s) = s'`
      `valid_call_list cs' (targetnode a)` 
      `\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)`
      `valid_return_list rs' (targetnode a)` `length rs' = length cs'` this]
    obtain ms ms'' s'' as' ms' as'' where "length ms = length cs'"
      and "n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
                     =slice_edges n\<^isub>c cs' as\<Rightarrow>* (ms'',s'')" 
      and paths:"n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s')"
      "ms = targetnodes rs'"
      "\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))"
      "slice_edges n\<^isub>c cs' as = slice_edges n\<^isub>c cs' as''"
      "targetnode a -as'' @ as'\<rightarrow>* m'" "valid_path_aux cs' (as'' @ as')"
      by blast
    from `\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))`
      `length ms = length cs'`
    have "\<forall>mx \<in> set ms. return_node mx"
      by(auto simp:in_set_conv_nth call_of_return_node_def)
    from `valid_edge a` `valid_edge c'` `a \<in> get_return_edges c'`
    have "return_node (targetnode a)" by(fastsimp simp:return_node_def)
    with `valid_edge c'` `valid_edge a` `a \<in> get_return_edges c'`
    have "call_of_return_node (targetnode a) (sourcenode c')"
      by(simp add:call_of_return_node_def) blast
    show ?case
    proof(cases "(\<forall>m \<in> set (targetnode a#ms). \<exists>m'. call_of_return_node m m' \<and> 
	m' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>)")
      case True
      then obtain x where "call_of_return_node (targetnode a) x"
	and "x \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" by fastsimp
      with `call_of_return_node (targetnode a) (sourcenode c')`
      have "sourcenode c' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>" by fastsimp
      with True `\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))`
	`length ms = length cs'` `cs = c' # cs'` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
      have "slice_edge n\<^isub>c cs a"
	apply(auto simp:slice_edge_def in_set_conv_nth) 
	by(erule_tac x="i" in allE) auto
      with `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f` `cs = c' # cs'`
      have "slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs' as" by simp
      from True `pred (kind a) s` `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	`\<forall>mx \<in> set ms. return_node mx` `length ms = length cs'` 
	`length s = Suc (length cs)` `m = sourcenode a`
	`length (transfer (kind a) s) = Suc (length cs')`
	`return_node (targetnode a)` `cs = c' # cs'`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) -a\<rightarrow> 
	(targetnode a#ms,transfer (kind a) s)"
	by(auto intro!:observable_move_return)
      with `length ms = length cs'` `length s = Suc (length cs)` `cs = c' # cs'`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =[]@[a]\<Rightarrow>
	(targetnode a#ms,transfer (kind a) s)"
	by(fastsimp intro:observable_moves_snoc silent_moves_Nil)
      with `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
                     =slice_edges n\<^isub>c cs' as\<Rightarrow>* (ms'',s'')`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) 
	=last [a]#slice_edges n\<^isub>c cs' as\<Rightarrow>* (ms'',s'')"
	by -(rule tom_Cons,auto)
      with `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs' as`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>* 
	(ms'',s'')" by simp
      moreover
      from `slice_edges n\<^isub>c cs' as = slice_edges n\<^isub>c cs' as''`
	`slice_edge n\<^isub>c cs a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f` `cs = c' # cs'`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs (a#as'')" by simp
      ultimately show ?thesis
	using paths `m = sourcenode a` `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	  `length ms = length cs'` `ms = targetnodes rs'` `cs = c' # cs'`
	  `slice_edges n\<^isub>c cs (a#as) = a#slice_edges n\<^isub>c cs' as`
	  `a \<in> get_return_edges c'` 
	  `call_of_return_node (targetnode a) (sourcenode c')`
	apply(rule_tac x="targetnode a#ms" in exI)
	apply(rule_tac x="ms''" in exI)
	apply(rule_tac x="s''" in exI)
	apply(rule_tac x="as'" in exI)
	apply(rule_tac x="ms'" in exI)
	apply(rule_tac x="a#as''" in exI)
	apply(auto intro:Cons_path simp:targetnodes_def)
	by(case_tac i) auto
    next
      case False
      with `\<forall>mx \<in> set ms. return_node mx` `return_node (targetnode a)`
      have "\<exists>m \<in> set (targetnode a # ms). \<exists>m'. call_of_return_node m m' \<and> 
	m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
	by(fastsimp dest:return_node_call_of_return_node)
      with `\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))`
	`length ms = length cs'` `cs = c' # cs'` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	`call_of_return_node (targetnode a) (sourcenode c')`
      have "\<not> slice_edge n\<^isub>c cs a"
	apply(auto simp:slice_edge_def in_set_conv_nth)
	by(erule_tac x="i" in allE) auto
      with `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f` `cs = c' # cs'`
      have "slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs' as" by simp
      from `pred (kind a) s` `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	`\<forall>mx \<in> set ms. return_node mx` `length ms = length cs'` 
	`length s = Suc (length cs)` `m = sourcenode a`
	`length (transfer (kind a) s) = Suc (length cs')`
	`return_node (targetnode a)` `cs = c' # cs'`
	`\<exists>m \<in> set (targetnode a # ms). \<exists>m'. call_of_return_node m m' \<and> 
	m' \<notin> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
      have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) -a\<rightarrow>\<^isub>\<tau>
	(targetnode a#ms,transfer (kind a) s)"
	by(auto intro!:silent_move_return)
      from `n\<^isub>c,kind \<turnstile> (targetnode a # ms,transfer (kind a) s) 
                     =slice_edges n\<^isub>c cs' as\<Rightarrow>* (ms'',s'')`
      show ?thesis
      proof(rule trans_observable_moves.cases)
	fix msx sx n\<^isub>c' f'
	assume "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" and "slice_edges n\<^isub>c cs' as = []"
	  and [simp]:"ms'' = msx" "s'' = sx" and "length msx = length sx"
	from `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs' as` 
	  `slice_edges n\<^isub>c cs' as = []`
	have "slice_edges n\<^isub>c cs (a#as) = []" by simp
	with `length ms = length cs'` `length s = Suc (length cs)` `cs = c' # cs'`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =slice_edges n\<^isub>c cs (a#as)\<Rightarrow>*
	                (sourcenode a#targetnode a#ms,s)"
	  by(fastsimp intro:tom_Nil)
	moreover
	from `n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')` `targetnode a # ms = msx`
	  `transfer (kind a) s = sx` `ms'' = msx` `s'' = sx`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) -a\<rightarrow>\<^isub>\<tau> 
	  (targetnode a#ms,transfer (kind a) s)`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
	  by(auto intro:silent_moves_Cons)
	from this `valid_edge a` 
	  `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
	  `valid_return_list rs m` `length rs = length cs`
	  `length s = Suc (length cs)` `m = sourcenode a`
	  `ms = targetnodes rs'` `rs = r'#rs'` `cs = c' # cs'`
	have "sourcenode a -a#as'\<rightarrow>* m'" and "valid_path_aux cs (a#as')"
	  by -(rule silent_moves_vpa_path,(fastsimp simp:targetnodes_def)+)+
	ultimately show ?thesis using `m = sourcenode a` `length ms = length cs'`
	  `\<forall>i<length cs'. call_of_return_node (ms ! i) (sourcenode (cs' ! i))`
	  `slice_edges n\<^isub>c cs (a#as) = []` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	  `n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =a#as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')`
	  `ms = targetnodes rs'` `rs = r'#rs'` `cs = c' # cs'`
	  `call_of_return_node (targetnode a) (sourcenode c')`
	  apply(rule_tac x="targetnode a#ms" in exI)
	  apply(rule_tac x="sourcenode a#targetnode a#ms" in exI)
	  apply(rule_tac x="s" in exI)
	  apply(rule_tac x="a#as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="[]" in exI)
	  apply(auto simp:targetnodes_def)
	  by(case_tac i) auto
      next
	fix n\<^isub>c' f' msx sx asx msx' sx' asx' msx'' sx''
	assume [simp]:"n\<^isub>c = n\<^isub>c'" and "kind = f'" and "targetnode a # ms = msx"
	  and "transfer (kind a) s = sx" 
	  and "slice_edges n\<^isub>c cs' as = last asx # asx'"
	  and "ms'' = msx''" and "s'' = sx''" 
	  and "n\<^isub>c',f' \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')"
	  and "n\<^isub>c',f' \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')"
	from `kind = f'` have [simp]:"f' = kind" by simp
	from `n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) -a\<rightarrow>\<^isub>\<tau> 
	  (targetnode a#ms,transfer (kind a) s)`
	  `n\<^isub>c',f' \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')`
	  `transfer (kind a) s = sx` `targetnode a # ms = msx`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =a#asx\<Rightarrow> (msx',sx')"
	  by(auto intro:silent_move_observable_moves)
	with `n\<^isub>c',f' \<turnstile> (msx',sx') =asx'\<Rightarrow>* (msx'',sx'')` `ms'' = msx''` `s'' = sx''`
	have "n\<^isub>c,kind \<turnstile> (sourcenode a#targetnode a#ms,s) =last (a#asx)#asx'\<Rightarrow>* 
	  (ms'',s'')"
	  by(fastsimp intro:trans_observable_moves.tom_Cons)
	moreover
	from `n\<^isub>c',f' \<turnstile> (msx,sx) =asx\<Rightarrow> (msx',sx')` have "asx \<noteq> []"
	  by(fastsimp elim:observable_moves.cases)
	with `slice_edges n\<^isub>c cs (a#as) = slice_edges n\<^isub>c cs' as`
	  `slice_edges n\<^isub>c cs' as = last asx # asx'`
	have "slice_edges n\<^isub>c cs (a#as) = last (a#asx)#asx'" by simp
	moreover
	from `\<not> slice_edge n\<^isub>c cs a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	  `slice_edges n\<^isub>c cs' as = slice_edges n\<^isub>c cs' as''` `cs = c' # cs'`
	have "slice_edges n\<^isub>c cs (a # as) = slice_edges n\<^isub>c cs (a # as'')" by simp
	ultimately show ?thesis using paths `m = sourcenode a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
	  `length ms = length cs'` `ms = targetnodes rs'` `valid_edge a`
	  `rs = r'#rs'` `cs = c' # cs'` `r' \<in> get_return_edges c'`
	  `call_of_return_node (targetnode a) (sourcenode c')`
	  apply(rule_tac x="targetnode a#ms" in exI)
	  apply(rule_tac x="ms''" in exI)
	  apply(rule_tac x="s''" in exI)
	  apply(rule_tac x="as'" in exI)
	  apply(rule_tac x="ms'" in exI)
	  apply(rule_tac x="a#as''" in exI)
	  apply(auto intro:Cons_path simp:targetnodes_def)
	  by(case_tac i) auto
      qed
    qed
  qed
qed



lemma valid_path_trans_observable_moves:
  assumes "m -as\<rightarrow>\<^isub>\<surd>* m'" and "preds (kinds as) [cf]" 
  and "transfers (kinds as) [cf] = s'"
  obtains ms'' s'' ms' as' as'' 
  where "n\<^isub>c,kind \<turnstile> ([m],[cf]) =slice_edges n\<^isub>c [] as\<Rightarrow>* (ms'',s'')"
  and "n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',s')"
  and "slice_edges n\<^isub>c [] as = slice_edges n\<^isub>c [] as''"
  and "m -as''@as'\<rightarrow>\<^isub>\<surd>* m'"
proof(atomize_elim)
  from `m -as\<rightarrow>\<^isub>\<surd>* m'` have "valid_path_aux [] as" and "m -as\<rightarrow>* m'"
    by(simp_all add:vp_def valid_path_def)
  from this `preds (kinds as) [cf]` `transfers (kinds as) [cf] = s'`
  show "\<exists>ms'' s'' as' ms' as''. 
    n\<^isub>c,kind \<turnstile> ([m],[cf]) =slice_edges n\<^isub>c [] as\<Rightarrow>* (ms'',s'') \<and>
    n\<^isub>c,kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m' # ms',s') \<and>
    slice_edges n\<^isub>c [] as = slice_edges n\<^isub>c [] as'' \<and> m -as'' @ as'\<rightarrow>\<^isub>\<surd>* m'"
    by -(erule vpa_trans_observable_moves[of _ _ _ _ _ _ "[]" n\<^isub>c],
      auto simp:valid_call_list_def valid_return_list_def vp_def valid_path_def)
qed


lemma WS_weak_sim_trans:
  assumes "((ms\<^isub>1,s\<^isub>1),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c"
  and "n\<^isub>c,kind \<turnstile> (ms\<^isub>1,s\<^isub>1) =as\<Rightarrow>* (ms\<^isub>1',s\<^isub>1')" and "as \<noteq> []"
  shows "((ms\<^isub>1',s\<^isub>1'),(ms\<^isub>1',transfers (slice_kinds n\<^isub>c as) s\<^isub>2)) \<in> WS n\<^isub>c \<and> 
         n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =as\<Rightarrow>* (ms\<^isub>1',transfers (slice_kinds n\<^isub>c as) s\<^isub>2)"
proof -
  obtain f where "f = kind" by simp
  with `n\<^isub>c,kind \<turnstile> (ms\<^isub>1,s\<^isub>1) =as\<Rightarrow>* (ms\<^isub>1',s\<^isub>1')` 
  have "n\<^isub>c,f \<turnstile> (ms\<^isub>1,s\<^isub>1) =as\<Rightarrow>* (ms\<^isub>1',s\<^isub>1')" by simp
  from `n\<^isub>c,f \<turnstile> (ms\<^isub>1,s\<^isub>1) =as\<Rightarrow>* (ms\<^isub>1',s\<^isub>1')` `((ms\<^isub>1,s\<^isub>1),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c` 
    `as \<noteq> []` `f = kind`
  show ?thesis
  proof(induct arbitrary:ms\<^isub>2 s\<^isub>2 rule:trans_observable_moves.induct)
    case tom_Nil thus ?case by simp
  next
    case (tom_Cons n\<^isub>c f ms s as ms' s' as' ms'' s'')
    note IH = `\<And>ms\<^isub>2 s\<^isub>2. \<lbrakk>((ms',s'),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c; as' \<noteq> []; f = kind\<rbrakk>
      \<Longrightarrow> ((ms'',s''),(ms'',transfers (slice_kinds n\<^isub>c as') s\<^isub>2)) \<in> WS n\<^isub>c \<and>
      n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =as'\<Rightarrow>* (ms'',transfers (slice_kinds n\<^isub>c as') s\<^isub>2)`
    from `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')` have "s' \<noteq> []"
      by(fastsimp elim:observable_moves.cases observable_move.cases)
    from `n\<^isub>c,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')`
    obtain asx ax msx sx where "n\<^isub>c,f \<turnstile> (ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)"
      and "n\<^isub>c,f \<turnstile> (msx,sx) -ax\<rightarrow> (ms',s')" and "as = asx@[ax]"
      by(fastsimp elim:observable_moves.cases)
    from `n\<^isub>c,f \<turnstile> (ms,s) =asx\<Rightarrow>\<^isub>\<tau> (msx,sx)` `((ms,s),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c` `f = kind`
    have "((msx,sx),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c" by(fastsimp intro:WS_silent_moves)
    from `((msx,sx),(ms\<^isub>2,s\<^isub>2)) \<in> WS n\<^isub>c` `n\<^isub>c,f \<turnstile> (msx,sx) -ax\<rightarrow> (ms',s')` `s' \<noteq> []`
      `f = kind`
    obtain asx' where "((ms',s'),(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)) \<in> WS n\<^isub>c"
      and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =asx'@[ax]\<Rightarrow> 
      (ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)"
      by(fastsimp elim:WS_observable_move)
    show ?case
    proof(cases "as' = []")
      case True
      with `n\<^isub>c,f \<turnstile> (ms',s') =as'\<Rightarrow>* (ms'',s'')` have "ms' = ms'' \<and> s' = s''"
	by(fastsimp elim:trans_observable_moves.cases dest:observable_move_notempty)
      from `((ms',s'),(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)) \<in> WS n\<^isub>c`
      have "length ms' = length (transfer (slice_kind n\<^isub>c ax) s\<^isub>2)"
	by(fastsimp elim:WS.cases)
      with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =asx'@[ax]\<Rightarrow> 
	(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)`
      have "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =(last (asx'@[ax]))#[]\<Rightarrow>* 
	(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)"
	by(fastsimp intro:trans_observable_moves.intros)
      with `((ms',s'),(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)) \<in> WS n\<^isub>c` `as = asx@[ax]`
	`ms' = ms'' \<and> s' = s''` True
      show ?thesis by(fastsimp simp:slice_kinds_def)
    next
      case False
      from IH[OF `((ms',s'),(ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)) \<in> WS n\<^isub>c` this 
	`f = kind`]
      have "((ms'',s''),(ms'',transfers (slice_kinds n\<^isub>c as') 
	(transfer (slice_kind n\<^isub>c ax) s\<^isub>2))) \<in> WS n\<^isub>c"
	and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2) =as'\<Rightarrow>* 
	(ms'',transfers (slice_kinds n\<^isub>c as') (transfer (slice_kind n\<^isub>c ax) s\<^isub>2))" 
	by simp_all
      with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =asx'@[ax]\<Rightarrow> 
                               (ms',transfer (slice_kind n\<^isub>c ax) s\<^isub>2)`
      have "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (ms\<^isub>2,s\<^isub>2) =(last (asx'@[ax]))#as'\<Rightarrow>* 
	(ms'',transfers (slice_kinds n\<^isub>c as') (transfer (slice_kind n\<^isub>c ax) s\<^isub>2))"
	by(fastsimp intro:trans_observable_moves.tom_Cons)
      with `((ms'',s''),(ms'',transfers (slice_kinds n\<^isub>c as') 
	(transfer (slice_kind n\<^isub>c ax) s\<^isub>2))) \<in> WS n\<^isub>c` False `as = asx@[ax]`
      show ?thesis by(fastsimp simp:slice_kinds_def)
    qed
  qed
qed


lemma stacks_rewrite:
  assumes "valid_call_list cs m" and "valid_return_list rs m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)"
  and "length rs = length cs" and "ms = targetnodes rs"
  shows "\<forall>i<length cs. call_of_return_node (ms!i) (sourcenode (cs!i))"
proof
  fix i show "i < length cs \<longrightarrow>
    call_of_return_node (ms ! i) (sourcenode (cs ! i))"
  proof
    assume "i < length cs"
    with `\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)` `length rs = length cs`
    have "rs!i \<in> get_return_edges (cs!i)" by fastsimp
    from `valid_return_list rs m` have "\<forall>r \<in> set rs. valid_edge r"
      by(rule valid_return_list_valid_edges)
    with `i < length cs` `length rs = length cs`
    have "valid_edge (rs!i)" by(simp add:all_set_conv_all_nth)
    from `valid_call_list cs m` have "\<forall>c \<in> set cs. valid_edge c"
      by(rule valid_call_list_valid_edges)
    with `i < length cs` have "valid_edge (cs!i)" by(simp add:all_set_conv_all_nth)
    with `valid_edge (rs!i)` `rs!i \<in> get_return_edges (cs!i)` `ms = targetnodes rs`
      `i < length cs` `length rs = length cs`
    show "call_of_return_node (ms ! i) (sourcenode (cs ! i))"
      by(fastsimp simp:call_of_return_node_def return_node_def targetnodes_def)
  qed
qed


lemma slice_tom_preds_vp:
  assumes "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =as\<Rightarrow>* (m'#ms',s')" and "valid_node m"
  and "valid_call_list cs m" and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)"
  and "valid_return_list rs m" and "length rs = length cs" and "ms = targetnodes rs"
  and "\<forall>mx \<in> set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
  obtains as' cs' rs' where "preds (slice_kinds n\<^isub>c as') s" 
  and "slice_edges n\<^isub>c cs as' = as" and "m -as'\<rightarrow>* m'" and "valid_path_aux cs as'" 
  and "upd_cs cs as' = cs'" and "valid_node m'" and "valid_call_list cs' m'" 
  and "\<forall>i < length rs'. rs'!i \<in> get_return_edges (cs'!i)"
  and "valid_return_list rs' m'" and "length rs' = length cs'" 
  and "ms' = targetnodes rs'" and "transfers (slice_kinds n\<^isub>c as') s \<noteq> []"
  and "transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as')) s =
    transfers (slice_kinds n\<^isub>c as') s"
proof(atomize_elim)
  from assms show "\<exists>as' cs' rs'. preds (slice_kinds n\<^isub>c as') s \<and>
    slice_edges n\<^isub>c cs as' = as \<and> m -as'\<rightarrow>* m' \<and> valid_path_aux cs as' \<and>
    upd_cs cs as' = cs' \<and> valid_node m' \<and> valid_call_list cs' m' \<and>
    (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and> valid_return_list rs' m' \<and>
    length rs' = length cs' \<and> ms' = targetnodes rs' \<and> 
    transfers (slice_kinds n\<^isub>c as') s \<noteq> [] \<and> 
    transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as')) s =
    transfers (slice_kinds n\<^isub>c as') s"
  proof(induct n\<^isub>c f\<equiv>"slice_kind n\<^isub>c" msx\<equiv>"m#ms" s as msx'\<equiv>"m'#ms'" s'
    arbitrary:m ms cs rs rule:trans_observable_moves.induct)
    case (tom_Nil msx s n\<^isub>c f)
    from `length msx = length s` `msx = m # ms` have "s \<noteq> []" by(cases s) auto
    from `msx = m # ms` `msx = m' # ms'` have [simp]:"m = m'" "ms = ms'" by simp_all
    have "preds (slice_kinds n\<^isub>c []) s" by(fastsimp simp:slice_kinds_def)
    moreover
    have "slice_edges n\<^isub>c cs [] = []" by simp
    moreover
    from `valid_node m` have "m -[]\<rightarrow>* m'" by(fastsimp intro:empty_path)
    moreover
    have "valid_path_aux cs []" by simp
    moreover
    have "upd_cs cs [] = cs" by simp
    ultimately show ?case using `valid_call_list cs m` `valid_return_list rs m` 
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `length rs = length cs`
      `ms = targetnodes rs` `s \<noteq> []` `valid_node m`
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="cs" in exI)
      apply(rule_tac x="rs" in exI)
      by(clarsimp simp:slice_kinds_def)
  next
    case (tom_Cons n\<^isub>c f msx s as msx' s' as' msx'' sx'')
    note IH = `\<And>m ms cs rs. \<lbrakk>valid_node m; valid_call_list cs m;
      \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); valid_return_list rs m;
      length rs = length cs; ms = targetnodes rs; 
      \<forall>mx\<in>set ms. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>;
      f = slice_kind n\<^isub>c; msx' = m # ms; msx'' = m' # ms'\<rbrakk>
      \<Longrightarrow> \<exists>as'' cs' rs'. preds (slice_kinds n\<^isub>c as'') s' \<and>
      slice_edges n\<^isub>c cs as'' = as' \<and> m -as''\<rightarrow>* m' \<and> valid_path_aux cs as'' \<and>
      upd_cs cs as'' = cs' \<and> valid_node m' \<and> valid_call_list cs' m' \<and>
      (\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)) \<and>
      valid_return_list rs' m' \<and> length rs' = length cs' \<and> ms' = targetnodes rs' \<and>
      transfers (slice_kinds n\<^isub>c as'') s' \<noteq> [] \<and> 
      transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as'')) s' =
      transfers (slice_kinds n\<^isub>c as'') s'`
    note callstack = `\<forall>mx\<in>set ms.
      \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>`
    from `n\<^isub>c,f \<turnstile> (msx,s) =as\<Rightarrow> (msx',s')` `f = slice_kind n\<^isub>c` `msx = m # ms` 
    obtain asx ax xs s'' where "as = asx@[ax]" 
      and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')" 
      and "n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')"
      by(fastsimp elim:observable_moves.cases)
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')`
    obtain xs' ms'' where [simp]:"xs = sourcenode ax#xs'" "msx' = targetnode ax#ms''"
      by(cases xs)(auto elim!:observable_move.cases,case_tac list,auto)
    from `n\<^isub>c,f \<turnstile> (msx,s) =as\<Rightarrow> (msx',s')` tom_Cons
    obtain cs'' rs'' where results:"valid_node (targetnode ax)"
      "valid_call_list cs'' (targetnode ax)"
      "\<forall>i < length rs''. rs''!i \<in> get_return_edges (cs''!i)"
      "valid_return_list rs'' (targetnode ax)" "length rs'' = length cs''" 
      "ms'' = targetnodes rs''" and "upd_cs cs as = cs''"
      by(auto elim!:observable_moves_preserves_stack)
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')` callstack
    have "\<forall>a \<in> set asx. intra_kind (kind a)"
      by simp(rule silent_moves_slice_intra_path)
    with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')`
    have [simp]:"xs' = ms" by(fastsimp dest:silent_moves_intra_path)
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')`
    have "\<forall>mx \<in> set ms''. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice n\<^isub>c\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastsimp dest:observable_set_stack_in_slice)
    from IH[OF results this `f = slice_kind n\<^isub>c` `msx' = targetnode ax#ms''` 
      `msx'' = m'#ms'`]
    obtain asx' cs' rs' where "preds (slice_kinds n\<^isub>c asx') s'" 
      and "slice_edges n\<^isub>c cs'' asx' = as'" and "targetnode ax -asx'\<rightarrow>* m'"
      and "valid_path_aux cs'' asx'" and "upd_cs cs'' asx' = cs'"
      and "valid_node m'" and "valid_call_list cs' m'" 
      and "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
      and "valid_return_list rs' m'" and "length rs' = length cs'"
      and "ms' = targetnodes rs'" and "transfers (slice_kinds n\<^isub>c asx') s' \<noteq> []"
      and trans_eq:"transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs'' asx')) s' =
      transfers (slice_kinds n\<^isub>c asx') s'"
      by blast
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')`
    have "preds (slice_kinds n\<^isub>c asx) s" and "transfers (slice_kinds n\<^isub>c asx) s = s''"
      by(auto intro:silent_moves_preds_transfers simp:slice_kinds_def)
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')`
    have "pred (slice_kind n\<^isub>c ax) s''" and "transfer (slice_kind n\<^isub>c ax) s'' = s'"
      by(auto elim:observable_move.cases)
    with `preds (slice_kinds n\<^isub>c asx) s` `as = asx@[ax]`
      `transfers (slice_kinds n\<^isub>c asx) s = s''`
    have "preds (slice_kinds n\<^isub>c as) s" by(simp add:preds_split slice_kinds_def)
    from `transfers (slice_kinds n\<^isub>c asx) s = s''` 
      `transfer (slice_kind n\<^isub>c ax) s'' = s'` `as = asx@[ax]`
    have "transfers (slice_kinds n\<^isub>c as) s = s'" 
      by(simp add:transfers_split slice_kinds_def)
    with `preds (slice_kinds n\<^isub>c asx') s'` `preds (slice_kinds n\<^isub>c as) s`
    have "preds (slice_kinds n\<^isub>c (as@asx')) s" by(simp add:preds_split slice_kinds_def)
    moreover
    from `valid_call_list cs m` `valid_return_list rs m`
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `length rs = length cs`
      `ms = targetnodes rs`
    have "\<forall>i<length cs. call_of_return_node (ms!i) (sourcenode (cs!i))"
      by(rule stacks_rewrite)
    with `n\<^isub>c,f \<turnstile> (msx,s) =as\<Rightarrow> (msx',s')` `msx = m # ms` `ms = targetnodes rs`
      `length rs = length cs`
    have "slice_edges n\<^isub>c cs as = [last as]"
      by(fastsimp elim:observable_moves_singular_slice_edge)
    with `slice_edges n\<^isub>c cs'' asx' = as'` `upd_cs cs as = cs''`
    have "slice_edges n\<^isub>c cs (as@asx') = [last as]@as'"
      by(fastsimp intro:slice_edges_Append)
    moreover
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')` `valid_node m`
      `valid_call_list cs m` `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
      `valid_return_list rs m` `length rs = length cs` `ms = targetnodes rs`
    have "m -asx\<rightarrow>* sourcenode ax" by(fastsimp intro:silent_moves_vpa_path)
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')` have "valid_edge ax"
      by(fastsimp elim:observable_move.cases)
    hence "sourcenode ax -[ax]\<rightarrow>* targetnode ax" by(rule path_edge)
    with `m -asx\<rightarrow>* sourcenode ax` `as = asx@[ax]`
    have "m -as\<rightarrow>* targetnode ax" by(fastsimp intro:path_Append)
    with `targetnode ax -asx'\<rightarrow>* m'` have "m -as@asx'\<rightarrow>* m'"
      by -(rule path_Append)
    moreover
    from `\<forall>a \<in> set asx. intra_kind (kind a)` have "valid_path_aux cs asx"
      by(rule valid_path_aux_intra_path)
    from `\<forall>a \<in> set asx. intra_kind (kind a)` have "upd_cs cs asx = cs"
      by(rule upd_cs_intra_path)
    from `m -asx\<rightarrow>* sourcenode ax` `\<forall>a \<in> set asx. intra_kind (kind a)`
    have "get_proc m = get_proc (sourcenode ax)"
      by(fastsimp intro:intra_path_get_procs simp:intra_path_def)
    with `valid_return_list rs m` have "valid_return_list rs (sourcenode ax)"
      apply(clarsimp simp:valid_return_list_def)
      apply(erule_tac x="cs'" in allE) apply clarsimp
      by(case_tac cs') auto
    with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')` `valid_edge ax` 
      `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)` `ms = targetnodes rs`
      `length rs = length cs`
    have "valid_path_aux cs [ax]"
      by(auto intro!:observable_move_vpa_path simp del:valid_path_aux.simps)
    with `valid_path_aux cs asx` `upd_cs cs asx = cs` `as = asx@[ax]`
    have "valid_path_aux cs as" by(fastsimp intro:valid_path_aux_Append)
    with `upd_cs cs as = cs''` `valid_path_aux cs'' asx'`
    have "valid_path_aux cs (as@asx')" by(fastsimp intro:valid_path_aux_Append)
    moreover
    from `upd_cs cs as = cs''` `upd_cs cs'' asx' = cs'`
    have "upd_cs cs (as@asx') = cs'" by(rule upd_cs_Append)
    moreover
    from `transfers (slice_kinds n\<^isub>c as) s = s'` 
      `transfers (slice_kinds n\<^isub>c asx') s' \<noteq> []`
    have "transfers (slice_kinds n\<^isub>c (as@asx')) s \<noteq> []"
      by(simp add:slice_kinds_def transfers_split)
    moreover
    from `n\<^isub>c,f \<turnstile> (msx,s) =as\<Rightarrow> (msx',s')` `f = slice_kind n\<^isub>c`
    have "transfers (map (slice_kind n\<^isub>c) as) s = s'"
      by simp(rule observable_moves_preds_transfers)
    from `n\<^isub>c,f \<turnstile> (msx,s) =as\<Rightarrow> (msx',s')` `msx = m # ms` `ms = targetnodes rs`
      `length rs = length cs` `\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)`
      `valid_call_list cs m` `valid_return_list rs m`
    have "slice_edges n\<^isub>c cs as = [last as]"
      by(fastsimp intro!:observable_moves_singular_slice_edge
      [OF _ _ _ stacks_rewrite])
    from `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (m#ms,s) =asx\<Rightarrow>\<^isub>\<tau> (xs,s'')` callstack
    have "s = s''" by(fastsimp intro:silent_moves_slice_keeps_state)
    with `n\<^isub>c,slice_kind n\<^isub>c \<turnstile> (xs,s'') -ax\<rightarrow> (msx',s')`
    have "transfer (slice_kind n\<^isub>c ax) s = s'" by(fastsimp elim:observable_move.cases)
    with `slice_edges n\<^isub>c cs as = [last as]` `as = asx@[ax]`
    have "s' = transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as)) s"
      by(simp add:slice_kinds_def)
    from `upd_cs cs as = cs''`
    have "slice_edges n\<^isub>c cs (as @ asx') =
      (slice_edges n\<^isub>c cs as)@(slice_edges n\<^isub>c cs'' asx')"
      by(fastsimp intro:slice_edges_Append)
    hence trans_eq':"transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs (as @ asx'))) s =
      transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs'' asx'))
        (transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as)) s)"
      by(simp add:slice_kinds_def transfers_split)
    from `s' = transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as)) s`
      `transfers (map (slice_kind n\<^isub>c) as) s = s'`
    have "transfers (map (slice_kind n\<^isub>c) (slice_edges n\<^isub>c cs as)) s =
      transfers (map (slice_kind n\<^isub>c) as) s"
      by(simp add:slice_kinds_def)
    with trans_eq trans_eq'
      `s' = transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs as)) s`
    have "transfers (slice_kinds n\<^isub>c (slice_edges n\<^isub>c cs (as @ asx'))) s =
       transfers (slice_kinds n\<^isub>c (as @ asx')) s" 
      by(simp add:slice_kinds_def transfers_split)
    ultimately show ?case
      using `valid_node m'` `valid_call_list cs' m'` 
	`\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)` 
	`valid_return_list rs' m'` `length rs' = length cs'` `ms' = targetnodes rs'`
      apply(rule_tac x="as@asx'" in exI)
      apply(rule_tac x="cs'" in exI)
      apply(rule_tac x="rs'" in exI)
      by clarsimp
  qed
qed


subsection {* The fundamental property of static interprocedural slicing *}

theorem fundamental_property_of_static_slicing:
  assumes "m -as\<rightarrow>\<^isub>\<surd>* m'" and "preds (kinds as) [cf]"
  obtains as' where "preds (slice_kinds (CFG_node m') as') [cf]"
  and "\<forall>V \<in> Use m'. state_val (transfers (slice_kinds (CFG_node m') as') [cf]) V = 
                    state_val (transfers (kinds as) [cf]) V"
  and "slice_edges (CFG_node m') [] as = slice_edges (CFG_node m') [] as'"
  and "transfers (kinds as) [cf] \<noteq> []"
  and "m -as'\<rightarrow>\<^isub>\<surd>* m'"
proof(atomize_elim)
  from `m -as\<rightarrow>\<^isub>\<surd>* m'` `preds (kinds as) [cf]` obtain ms'' s'' ms' as' as''
    where "CFG_node m',kind \<turnstile> ([m],[cf]) =slice_edges (CFG_node m') [] as\<Rightarrow>* 
                              (ms'',s'')"
    and "CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])"
    and "slice_edges (CFG_node m') [] as = slice_edges (CFG_node m') [] as''"
    and "m -as''@as'\<rightarrow>\<^isub>\<surd>* m'"
    by(auto elim:valid_path_trans_observable_moves[of _ _ _ _ _ "CFG_node m'"])
  from `m -as\<rightarrow>\<^isub>\<surd>* m'` have "valid_node m" and "valid_node m'"
    by(auto intro:path_valid_node simp:vp_def)
  hence "CFG_node m' \<in> HRB_slice (CFG_node m')" by -(rule HRB_slice_refl)
  from `valid_node m` have "(([m],[cf]),([m],[cf])) \<in> WS (CFG_node m')" 
    by(fastsimp intro:WSI)
  { fix V assume "V \<in> Use m'"
    with `valid_node m'` have "V \<in> Use\<^bsub>SDG\<^esub> (CFG_node m')" 
      by(fastsimp intro:CFG_Use_SDG_Use)
    moreover
    from `valid_node m'` 
    have "parent_node (CFG_node m') -[]\<rightarrow>\<^isub>\<iota>* parent_node (CFG_node m')" 
      by(fastsimp intro:empty_path simp:intra_path_def)
    ultimately have "V \<in> rv (CFG_node m') (CFG_node m')" 
      using `CFG_node m' \<in> HRB_slice (CFG_node m')`
      by(fastsimp intro:rvI simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use m'. V \<in> rv (CFG_node m') (CFG_node m')" by simp
  show "\<exists>as'. preds (slice_kinds (CFG_node m') as') [cf] \<and>
    (\<forall>V\<in>Use m'. state_val (transfers (slice_kinds (CFG_node m') as') [cf]) V =
    state_val (transfers (kinds as) [cf]) V) \<and> 
    slice_edges (CFG_node m') [] as = slice_edges (CFG_node m') [] as' \<and>
     transfers (kinds as) [cf] \<noteq> [] \<and> m -as'\<rightarrow>\<^isub>\<surd>* m'"
  proof(cases "slice_edges (CFG_node m') [] as = []")
    case True
    hence "preds (slice_kinds (CFG_node m') []) [cf]" 
      and "slice_edges (CFG_node m') [] [] = slice_edges (CFG_node m') [] as"
      by(simp_all add:slice_kinds_def)
    with `CFG_node m',kind \<turnstile> ([m],[cf]) =slice_edges (CFG_node m') [] as\<Rightarrow>* 
      (ms'',s'')`
    have [simp]:"ms'' = [m]" "s'' = [cf]" by(auto elim:trans_observable_moves.cases)
    with `CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
    have "CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])"
      by simp
    with `valid_node m` have "m -as'\<rightarrow>* m'" and "valid_path_aux [] as'"
      by(auto intro:silent_moves_vpa_path[of _ _ _ _ _ _ _ _ _ "[]"]
	       simp:targetnodes_def valid_return_list_def)
    hence "m -as'\<rightarrow>\<^isub>\<surd>* m'" by(simp add:vp_def valid_path_def)
    from `CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
    have "slice_edges (CFG_node m') [] as' = []"
      by(fastsimp dest:silent_moves_no_slice_edges[where cs="[]" and rs="[]"]
                  simp:targetnodes_def)
    from `CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
      `valid_node m` `valid_node m'`
    have returns:"\<forall>mx \<in> set ms'. 
      \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>"
      by -(erule silent_moves_called_node_in_slice1_nodestack_in_slice1
      [of _ _ _ _ _ _ _ _ "[]" "[]"],
	auto intro:refl_slice1 simp:targetnodes_def valid_return_list_def)
    from `CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
      `(([m],[cf]),([m],[cf])) \<in> WS (CFG_node m')` 
    have WS:"((m'#ms',transfers (kinds as) [cf]),([m],[cf])) \<in> WS (CFG_node m')"
      by(rule WS_silent_moves)
    hence "transfers (kinds as) [cf] \<noteq> []" by(auto elim!:WS.cases)
    with WS returns `transfers (kinds as) [cf] \<noteq> []` 
    have "\<forall>V \<in> rv (CFG_node m') (CFG_node m'). 
      state_val (transfers (kinds as) [cf]) V = fst cf V"
      apply - apply(erule WS.cases) apply clarsimp
      by(case_tac msx)(auto simp:hd_conv_nth)
    with `\<forall>V \<in> Use m'. V \<in> rv (CFG_node m') (CFG_node m')`
    have Uses:"\<forall>V \<in> Use m'. state_val (transfers (kinds as) [cf]) V = fst cf V"
      by simp
    have [simp]:"ms' = []"
    proof(rule ccontr)
      assume "ms' \<noteq> []"
      with `CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
	`valid_node m` `valid_node m'`
      show False
	by(fastsimp elim:silent_moves_nonempty_nodestack_False intro:refl_slice1)
    qed
    with `CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
    have "CFG_node m',kind \<turnstile> ([m],[cf]) =as'\<Rightarrow>\<^isub>\<tau> ([m'],transfers (kinds as) [cf])"
      by simp
    with `valid_node m` have "m -as'\<rightarrow>\<^bsub>sl\<^esub>* m'"
      by(auto dest!:silent_moves_slp simp:valid_call_list_def valid_return_list_def 
	targetnodes_def slp_def same_level_path_def)
    from this `slice_edges (CFG_node m') [] as' = []` 
    obtain asx where "m -asx\<rightarrow>\<^isub>\<iota>* m'" and "slice_edges (CFG_node m') [] asx = []"
      by(erule slp_to_intra_path_with_slice_edges)
    with `CFG_node m' \<in> HRB_slice (CFG_node m')`
    obtain asx' where "m -asx'\<rightarrow>\<^isub>\<iota>* m'" 
      and "preds (slice_kinds (CFG_node m') asx') [cf]"
      and "slice_edges (CFG_node m') [] asx' = []"
      by -(erule exists_sliced_intra_path_preds,auto simp:SDG_to_CFG_set_def)
    from `m -asx'\<rightarrow>\<^isub>\<iota>* m'` have "m -asx'\<rightarrow>\<^isub>\<surd>* m'" by(rule intra_path_vp)
    from Uses `slice_edges (CFG_node m') [] asx' = []`
    have "hd (transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] asx')) [cf]) = cf" by(simp add:slice_kinds_def)
    from `m -asx'\<rightarrow>\<^isub>\<iota>* m'`
    have "transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] asx')) [cf] = 
      transfers (slice_kinds (CFG_node m') asx') [cf]"
      by(fastsimp intro:transfers_intra_slice_kinds_slice_edges simp:intra_path_def)
    with `hd (transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] asx')) [cf]) = cf`
    have "hd (transfers (slice_kinds (CFG_node m') asx') [cf]) = cf" by simp
    with Uses have "\<forall>V\<in>Use m'. 
      state_val (transfers (slice_kinds (CFG_node m') asx') [cf]) V =
      state_val (transfers (kinds as) [cf]) V" by simp
    with `m -asx'\<rightarrow>\<^isub>\<surd>* m'` `preds (slice_kinds (CFG_node m') asx') [cf]`
      `slice_edges (CFG_node m') [] asx' = []` `transfers (kinds as) [cf] \<noteq> []` True
    show ?thesis by fastsimp
  next
    case False
    with `(([m],[cf]),([m],[cf])) \<in> WS (CFG_node m')`
      `CFG_node m',kind \<turnstile> ([m],[cf]) =slice_edges (CFG_node m') [] as\<Rightarrow>* (ms'',s'')`
    have WS:"((ms'',s''),(ms'',transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] as)) [cf])) \<in> WS (CFG_node m')"
      and tom:"CFG_node m',slice_kind (CFG_node m') \<turnstile> ([m],[cf]) 
      =slice_edges (CFG_node m') [] as\<Rightarrow>* 
      (ms'',transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] as)) [cf])"
      by(fastsimp dest:WS_weak_sim_trans)+
    from WS obtain mx msx where [simp]:"ms'' = mx#msx" and "valid_node mx"
      by -(erule WS.cases,cases ms'',auto)
    from `CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])` WS 
    have WS':"((m'#ms',transfers (kinds as) [cf]),
      (mx#msx,transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] as)) [cf])) \<in> WS (CFG_node m')"
      by simp(rule WS_silent_moves)
    from tom `valid_node m`
    obtain asx csx rsx where "preds (slice_kinds (CFG_node m') asx) [cf]"
      and "slice_edges (CFG_node m') [] asx = slice_edges (CFG_node m') [] as"
      and "m -asx\<rightarrow>\<^isub>\<surd>* mx" and "transfers (slice_kinds (CFG_node m') asx) [cf] \<noteq> []"
      and "upd_cs [] asx = csx" and stack:"valid_node mx" "valid_call_list csx mx" 
      "\<forall>i < length rsx. rsx!i \<in> get_return_edges (csx!i)"
      "valid_return_list rsx mx" "length rsx = length csx" 
      "msx = targetnodes rsx"
      and trans_eq:"transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] asx)) [cf] = 
      transfers (slice_kinds (CFG_node m') asx) [cf]"
      by(auto elim:slice_tom_preds_vp[of _ _ _ _ _ _ _ _ "[]" "[]"]
	      simp:valid_call_list_def valid_return_list_def targetnodes_def 
	           vp_def valid_path_def)
    from `transfers (slice_kinds (CFG_node m') asx) [cf] \<noteq> []`
    obtain cf' cfs' where eq:"transfers (slice_kinds (CFG_node m') asx) [cf] = 
      cf'#cfs'" by(cases "transfers (slice_kinds (CFG_node m') asx) [cf]") auto
    from WS' have callstack:"\<forall>mx \<in> set msx. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastsimp elim:WS.cases)
    with `CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
      `valid_node m'` stack
    have callstack':"\<forall>mx \<in> set ms'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>"
      by simp(erule silent_moves_called_node_in_slice1_nodestack_in_slice1
        [of _ _ _ _ _ _ _ _ rsx csx],auto intro:refl_slice1)
    with `CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
      stack callstack
    have "mx -as'\<rightarrow>\<^bsub>sl\<^esub>* m'" and "msx = ms'" by(auto dest!:silent_moves_slp)
    from `CFG_node m',kind \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^isub>\<tau> (m'#ms',transfers (kinds as) [cf])`
      stack
    have "slice_edges (CFG_node m') csx as' = []"
      by(auto dest:silent_moves_no_slice_edges[OF _ _ _ stacks_rewrite])
    with `mx -as'\<rightarrow>\<^bsub>sl\<^esub>* m'` obtain asx'' where "mx -asx''\<rightarrow>\<^isub>\<iota>* m'"
      and "slice_edges (CFG_node m') csx asx'' = []"
      by(erule slp_to_intra_path_with_slice_edges)
    from stack have "\<forall>i<length csx. call_of_return_node (msx!i) (sourcenode (csx!i))"
      by -(rule stacks_rewrite)
    with callstack `msx = targetnodes rsx` `length rsx = length csx`
    have "\<forall>c\<in>set csx. sourcenode c \<in> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>"
      by(auto simp:all_set_conv_all_nth targetnodes_def)
    with `mx -asx''\<rightarrow>\<^isub>\<iota>* m'` `slice_edges (CFG_node m') csx asx'' = []` `valid_node m'`
      eq
    obtain asx' where "mx -asx'\<rightarrow>\<^isub>\<iota>* m'"
      and "preds (slice_kinds (CFG_node m') asx') (cf'#cfs')"
      and "slice_edges (CFG_node m') csx asx' = []"
      by -(erule exists_sliced_intra_path_preds,
	auto intro:HRB_slice_refl simp:SDG_to_CFG_set_def)
    with eq have "preds (slice_kinds (CFG_node m') asx') 
      (transfers (slice_kinds (CFG_node m') asx) [cf])" by simp
    with `preds (slice_kinds (CFG_node m') asx) [cf]`
    have "preds (slice_kinds (CFG_node m') (asx@asx')) [cf]"
      by(simp add:slice_kinds_def preds_split)
    from `m -asx\<rightarrow>\<^isub>\<surd>* mx` `mx -asx'\<rightarrow>\<^isub>\<iota>* m'` have "m -asx@asx'\<rightarrow>\<^isub>\<surd>* m'"
      by(fastsimp elim:vp_slp_Append intra_path_slp)
    from `upd_cs [] asx = csx` `slice_edges (CFG_node m') csx asx' = []`
    have "slice_edges (CFG_node m') [] (asx@asx') = 
      (slice_edges (CFG_node m') [] asx)@[]"
      by(fastsimp intro:slice_edges_Append)
    from `mx -asx'\<rightarrow>\<^isub>\<iota>* m'` `\<forall>c\<in>set csx. sourcenode c \<in> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>`
    have trans_eq':
      "transfers (slice_kinds (CFG_node m') 
        (slice_edges (CFG_node m') csx asx')) 
          (transfers (slice_kinds (CFG_node m') asx) [cf]) =
      transfers (slice_kinds (CFG_node m') asx') 
        (transfers (slice_kinds (CFG_node m') asx) [cf])"
      by(fastsimp intro:transfers_intra_slice_kinds_slice_edges simp:intra_path_def) 
    from `upd_cs [] asx = csx`
    have "slice_edges (CFG_node m') [] (asx@asx') = 
      (slice_edges (CFG_node m') [] asx)@(slice_edges (CFG_node m') csx asx')"
      by(fastsimp intro:slice_edges_Append)
    hence "transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] (asx@asx'))) [cf] =
      transfers (slice_kinds (CFG_node m') (slice_edges (CFG_node m') csx asx'))
      (transfers (slice_kinds (CFG_node m') (slice_edges (CFG_node m') [] asx)) [cf])"
      by(simp add:slice_kinds_def transfers_split)
    with trans_eq have "transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] (asx@asx'))) [cf] =
      transfers (slice_kinds (CFG_node m') (slice_edges (CFG_node m') csx asx'))
      (transfers (slice_kinds (CFG_node m') asx) [cf])" by simp
    with trans_eq' have trans_eq'':"transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] (asx@asx'))) [cf] =
      transfers (slice_kinds (CFG_node m') (asx@asx')) [cf]" 
      by(simp add:slice_kinds_def transfers_split)
    from WS' obtain x xs where "m'#ms' = xs@x#msx"
      and "xs \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node x mx' \<and> 
      mx' \<notin> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>)"
      and rest:"\<forall>i < length (mx#msx). \<forall>V \<in> rv (CFG_node m') (CFG_node ((x#msx)!i)). 
      (fst ((transfers (kinds as) [cf])!(length xs + i))) V = 
      (fst ((transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] as)) [cf])!i)) V"
      "transfers (kinds as) [cf] \<noteq> []"
      "transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] as)) [cf] \<noteq> []"
      by(fastsimp elim:WS.cases)
    from `m'#ms' = xs@x#msx` `xs \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node x mx' \<and> 
      mx' \<notin> \<lfloor>HRB_slice (CFG_node m')\<rfloor>\<^bsub>CFG\<^esub>)` callstack'
    have [simp]:"xs = []" "x = m'" "ms' = msx" by(cases xs,auto)+
    from rest have "\<forall>V \<in> rv (CFG_node m') (CFG_node m').
      state_val (transfers (kinds as) [cf]) V = 
      state_val (transfers (slice_kinds (CFG_node m') 
        (slice_edges (CFG_node m') [] as)) [cf]) V"
      by(fastsimp dest:hd_conv_nth)
    with `\<forall>V \<in> Use m'. V \<in> rv (CFG_node m') (CFG_node m')` 
      `slice_edges (CFG_node m') [] asx = slice_edges (CFG_node m') [] as`
    have "\<forall>V \<in> Use m'. state_val (transfers (kinds as) [cf]) V = 
      state_val (transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] asx)) [cf]) V"
      by simp
    with `slice_edges (CFG_node m') [] (asx@asx') = 
      (slice_edges (CFG_node m') [] asx)@[]`
    have "\<forall>V \<in> Use m'. state_val (transfers (kinds as) [cf]) V = 
      state_val (transfers (slice_kinds (CFG_node m') 
      (slice_edges (CFG_node m') [] (asx@asx'))) [cf]) V"
      by simp
    with trans_eq'' have "\<forall>V \<in> Use m'. state_val (transfers (kinds as) [cf]) V = 
      state_val (transfers (slice_kinds (CFG_node m') (asx@asx')) [cf]) V"
      by simp
    with `preds (slice_kinds (CFG_node m') (asx@asx')) [cf]`
      `m -asx@asx'\<rightarrow>\<^isub>\<surd>* m'` `slice_edges (CFG_node m') [] (asx@asx') = 
      (slice_edges (CFG_node m') [] asx)@[]` `transfers (kinds as) [cf] \<noteq> []`
      `slice_edges (CFG_node m') [] asx = slice_edges (CFG_node m') [] as`
    show ?thesis by fastsimp
  qed
qed

end



subsection {* The fundamental property of static interprocedural slicing related to the semantics *}

locale SemanticsProperty = SDG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses +
  CFG_semantics_wf sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret) edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "(pname \<times> 'var list \<times> 'var list) list" and Main :: "pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list"
  and sem :: "'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> 'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51,0] 80)
begin


theorem fundamental_property_of_path_slicing_semantically:
  assumes identifies:"m \<triangleq> c" and reds:"\<langle>c,[cf]\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"
  obtains m' as cfs' where "m -as\<rightarrow>\<^isub>\<surd>* m'" and "m' \<triangleq> c'"
  and "preds (slice_kinds (CFG_node m') as) [(cf,undefined)]"
  and "\<forall>V \<in> Use m'. state_val (transfers (slice_kinds (CFG_node m') as) 
  [(cf,undefined)]) V = state_val cfs' V" and "map fst cfs' = s'"
proof(atomize_elim) 
  from identifies reds obtain m' as cfs' where path:"m -as\<rightarrow>\<^isub>\<surd>* m'"
    and transfers:"transfers (kinds as) [(cf,undefined)] = cfs'"
    and preds:"preds (kinds as) [(cf,undefined)]"
    and identifies':"m' \<triangleq> c'" and "map fst cfs' = s'"
    by(fastsimp dest:fundamental_property)
  from path preds obtain as'
    where preds':"preds (slice_kinds (CFG_node m') as') [(cf,undefined)]"
    and vals:"\<forall>V \<in> Use m'. state_val (transfers (slice_kinds (CFG_node m') as') 
    [(cf,undefined)]) V = state_val (transfers (kinds as) [(cf,undefined)]) V"
    and path':"m -as'\<rightarrow>\<^isub>\<surd>* m'"
    by -(erule fundamental_property_of_static_slicing)
  from transfers vals have "\<forall>V \<in> Use m'. 
    state_val (transfers (slice_kinds (CFG_node m') as') [(cf,undefined)]) V = 
    state_val cfs' V" by simp
  with preds' path' identifies' `map fst cfs' = s'`
  show "\<exists>as m' cfs'. m -as\<rightarrow>\<^isub>\<surd>* m' \<and> m' \<triangleq> c' \<and>
    preds (slice_kinds (CFG_node m') as) [(cf, undefined)] \<and>
    (\<forall>V\<in>Use m'. state_val (transfers (slice_kinds (CFG_node m') as) 
    [(cf, undefined)]) V = state_val cfs' V) \<and> map fst cfs' = s'"
    by blast
qed

end

end
    




