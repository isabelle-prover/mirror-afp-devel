section {* SDG *}

theory SDG imports CFGExit_wf Postdomination begin

subsection {* The nodes of the SDG *}

datatype 'node SDG_node = 
    CFG_node 'node
  | Formal_in  "'node \<times> nat"
  | Formal_out "'node \<times> nat"
  | Actual_in  "'node \<times> nat"
  | Actual_out "'node \<times> nat"

fun parent_node :: "'node SDG_node \<Rightarrow> 'node"
  where "parent_node (CFG_node n) = n"
  | "parent_node (Formal_in (m,x)) = m"
  | "parent_node (Formal_out (m,x)) = m"
  | "parent_node (Actual_in (m,x)) = m"
  | "parent_node (Actual_out (m,x)) = m"


locale SDG = CFGExit_wf sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses +
  Postdomination sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list"

begin


fun valid_SDG_node :: "'node SDG_node \<Rightarrow> bool"
  where "valid_SDG_node (CFG_node n) \<longleftrightarrow> valid_node n"
  | "valid_SDG_node (Formal_in (m,x)) \<longleftrightarrow>
  (\<exists>a Q r p fs ins outs. valid_edge a \<and> (kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> targetnode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length ins)"
  | "valid_SDG_node (Formal_out (m,x)) \<longleftrightarrow>
  (\<exists>a Q p f ins outs. valid_edge a \<and> (kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> sourcenode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length outs)"
  | "valid_SDG_node (Actual_in (m,x)) \<longleftrightarrow>
  (\<exists>a Q r p fs ins outs. valid_edge a \<and> (kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> sourcenode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length ins)"
  | "valid_SDG_node (Actual_out (m,x)) \<longleftrightarrow>
  (\<exists>a Q p f ins outs. valid_edge a \<and> (kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> targetnode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length outs)"


lemma valid_SDG_CFG_node: 
  "valid_SDG_node n \<Longrightarrow> valid_node (parent_node n)"
by(cases n) auto


lemma Formal_in_parent_det:
  assumes "valid_SDG_node (Formal_in (m,x))" and "valid_SDG_node (Formal_in (m',x'))"
  and "get_proc m = get_proc m'"
  shows "m = m'"
proof -
  from `valid_SDG_node (Formal_in (m,x))` obtain a Q r p fs ins outs
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length ins" by fastforce
  from `valid_SDG_node (Formal_in (m',x'))` obtain a' Q' r' p' f' ins' outs'
    where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'" and "targetnode a' = m'"
    and "(p',ins',outs') \<in> set procs" and "x' < length ins'" by fastforce
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `targetnode a = m`
  have "get_proc m = p" by(fastforce intro:get_proc_call)
  moreover
  from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'` `targetnode a' = m'`
  have "get_proc m' = p'" by(fastforce intro:get_proc_call)
  ultimately have "p = p'" using `get_proc m = get_proc m'` by simp
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'`
    `targetnode a = m` `targetnode a' = m'`
  show ?thesis by(fastforce intro:same_proc_call_unique_target)
qed


lemma valid_SDG_node_parent_Entry:
  assumes "valid_SDG_node n" and "parent_node n = (_Entry_)"
  shows "n = CFG_node (_Entry_)"
proof(cases n)
  case CFG_node with `parent_node n = (_Entry_)` show ?thesis by simp
next
  case (Formal_in z)
  with `parent_node n = (_Entry_)` obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with `valid_SDG_node n` Formal_in obtain a where "valid_edge a"
    and "targetnode a = (_Entry_)" by auto
  hence False by -(rule Entry_target,simp+)
  thus ?thesis by simp
next
  case (Formal_out z)
  with `parent_node n = (_Entry_)` obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with `valid_SDG_node n` Formal_out obtain a Q p f where "valid_edge a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and  "sourcenode a = (_Entry_)" by auto
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p"
    by(rule get_proc_return)
  with `sourcenode a = (_Entry_)` have "p = Main"
    by(auto simp:get_proc_Entry)
  with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have False
    by(fastforce intro:Main_no_return_source)
  thus ?thesis by simp
next
  case (Actual_in z)
  with `parent_node n = (_Entry_)` obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with `valid_SDG_node n` Actual_in obtain a Q r p fs where "valid_edge a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "sourcenode a = (_Entry_)" by fastforce
  hence False by -(rule Entry_no_call_source,auto)
  thus ?thesis by simp
next
  case (Actual_out z)
  with `parent_node n = (_Entry_)` obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with `valid_SDG_node n` Actual_out obtain a where "valid_edge a"
    "targetnode a = (_Entry_)" by auto
  hence False by -(rule Entry_target,simp+)
  thus ?thesis by simp
qed


lemma valid_SDG_node_parent_Exit:
  assumes "valid_SDG_node n" and "parent_node n = (_Exit_)"
  shows "n = CFG_node (_Exit_)"
proof(cases n)
  case CFG_node with `parent_node n = (_Exit_)` show ?thesis by simp
next
  case (Formal_in z)
  with `parent_node n = (_Exit_)` obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with `valid_SDG_node n` Formal_in obtain a Q r p fs where "valid_edge a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = (_Exit_)" by fastforce
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with `targetnode a = (_Exit_)` have "p = Main"
    by(auto simp:get_proc_Exit)
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have False
    by(fastforce intro:Main_no_call_target)
  thus ?thesis by simp
next
  case (Formal_out z)
  with `parent_node n = (_Exit_)` obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with `valid_SDG_node n` Formal_out obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by auto
  hence False by -(rule Exit_source,simp+)
  thus ?thesis by simp
next
  case (Actual_in z)
  with `parent_node n = (_Exit_)` obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with `valid_SDG_node n` Actual_in obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by auto
  hence False by -(rule Exit_source,simp+)
  thus ?thesis by simp
next
  case (Actual_out z)
  with `parent_node n = (_Exit_)` obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with `valid_SDG_node n` Actual_out obtain a Q p f where "valid_edge a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "targetnode a = (_Exit_)" by auto
  hence False by -(erule Exit_no_return_target,auto)
  thus ?thesis by simp
qed


subsection {* Data dependence *}

inductive SDG_Use :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" ("_ \<in> Use\<^bsub>SDG\<^esub> _")
where CFG_Use_SDG_Use:
  "\<lbrakk>valid_node m; V \<in> Use m; n = CFG_node m\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"
  | Actual_in_SDG_Use:
  "\<lbrakk>valid_SDG_node n; n = Actual_in (m,x); V \<in> (ParamUses m)!x\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"
  | Formal_out_SDG_Use:
  "\<lbrakk>valid_SDG_node n; n = Formal_out (m,x); get_proc m = p; (p,ins,outs) \<in> set procs;
    V = outs!x\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"


abbreviation notin_SDG_Use :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"  ("_ \<notin> Use\<^bsub>SDG\<^esub> _")
  where "V \<notin> Use\<^bsub>SDG\<^esub> n \<equiv> \<not> V \<in> Use\<^bsub>SDG\<^esub> n"


lemma in_Use_valid_SDG_node:
  "V \<in> Use\<^bsub>SDG\<^esub> n \<Longrightarrow> valid_SDG_node n"
by(induct rule:SDG_Use.induct,auto intro:valid_SDG_CFG_node)


lemma SDG_Use_parent_Use: 
  "V \<in> Use\<^bsub>SDG\<^esub> n \<Longrightarrow> V \<in> Use (parent_node n)"
proof(induct rule:SDG_Use.induct)
  case CFG_Use_SDG_Use thus ?case by simp
next
  case (Actual_in_SDG_Use n m x V)
  from `valid_SDG_node n` `n = Actual_in (m, x)` obtain a Q r p fs ins outs
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "sourcenode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length ins" by fastforce
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
  have "length(ParamUses (sourcenode a)) = length ins"
    by(fastforce intro:ParamUses_call_source_length)
  with `x < length ins`
  have "(ParamUses (sourcenode a))!x \<in> set (ParamUses (sourcenode a))" by simp
  with `V \<in> (ParamUses m)!x` `sourcenode a = m`
  have "V \<in> Union (set (ParamUses m))" by fastforce
  with `valid_edge a` `sourcenode a = m` `n = Actual_in (m, x)` show ?case
    by(fastforce intro:ParamUses_in_Use)
next
  case (Formal_out_SDG_Use n m x p ins outs V)
  from `valid_SDG_node n` `n = Formal_out (m, x)` obtain a Q p' f ins' outs'
    where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f" and "sourcenode a = m"
    and "(p',ins',outs') \<in> set procs" and "x < length outs'" by fastforce
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f` have "get_proc (sourcenode a) = p'"
    by(rule get_proc_return)
  with `get_proc m = p` `sourcenode a = m` have [simp]:"p = p'" by simp
  with `(p',ins',outs') \<in> set procs` `(p,ins,outs) \<in> set procs` unique_callers
  have [simp]:"ins' = ins" "outs' = outs" by(auto dest:distinct_fst_isin_same_fst)
  from `x < length outs'` `V = outs ! x` have "V \<in> set outs" by fastforce
  with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f` `(p,ins,outs) \<in> set procs`
  have "V \<in> Use (sourcenode a)" by(fastforce intro:outs_in_Use)
  with `sourcenode a = m` `valid_SDG_node n` `n = Formal_out (m, x)`
  show ?case by simp
qed



inductive SDG_Def :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" ("_ \<in> Def\<^bsub>SDG\<^esub> _")
where CFG_Def_SDG_Def:
  "\<lbrakk>valid_node m; V \<in> Def m; n = CFG_node m\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"
  | Formal_in_SDG_Def:
  "\<lbrakk>valid_SDG_node n; n = Formal_in (m,x); get_proc m = p; (p,ins,outs) \<in> set procs;
    V = ins!x\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"
  | Actual_out_SDG_Def:
  "\<lbrakk>valid_SDG_node n; n = Actual_out (m,x); V = (ParamDefs m)!x\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"

abbreviation notin_SDG_Def :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"  ("_ \<notin> Def\<^bsub>SDG\<^esub> _")
  where "V \<notin> Def\<^bsub>SDG\<^esub> n \<equiv> \<not> V \<in> Def\<^bsub>SDG\<^esub> n"


lemma in_Def_valid_SDG_node:
  "V \<in> Def\<^bsub>SDG\<^esub> n \<Longrightarrow> valid_SDG_node n"
by(induct rule:SDG_Def.induct,auto intro:valid_SDG_CFG_node)


lemma SDG_Def_parent_Def: 
  "V \<in> Def\<^bsub>SDG\<^esub> n \<Longrightarrow> V \<in> Def (parent_node n)"
proof(induct rule:SDG_Def.induct)
  case CFG_Def_SDG_Def thus ?case by simp
next
  case (Formal_in_SDG_Def n m x p ins outs V)
  from `valid_SDG_node n` `n = Formal_in (m, x)` obtain a Q r p' fs ins' outs'
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" and "targetnode a = m"
    and "(p',ins',outs') \<in> set procs" and "x < length ins'" by fastforce
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` have "get_proc (targetnode a) = p'"
    by(rule get_proc_call)
  with `get_proc m = p` `targetnode a = m` have [simp]:"p = p'" by simp
  with `(p',ins',outs') \<in> set procs` `(p,ins,outs) \<in> set procs` unique_callers
  have [simp]:"ins' = ins" "outs' = outs" by(auto dest:distinct_fst_isin_same_fst)
  from `x < length ins'` `V = ins ! x` have "V \<in> set ins" by fastforce
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `(p,ins,outs) \<in> set procs`
  have "V \<in> Def (targetnode a)" by(fastforce intro:ins_in_Def)
  with `targetnode a = m` `valid_SDG_node n` `n = Formal_in (m, x)`
  show ?case by simp
next
  case (Actual_out_SDG_Def n m x V)
  from `valid_SDG_node n` `n = Actual_out (m, x)` obtain a Q p f ins outs
    where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "targetnode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length outs" by fastforce
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs`
  have "length(ParamDefs (targetnode a)) = length outs" 
    by(rule ParamDefs_return_target_length)
  with `x < length outs` `V = ParamDefs m ! x` `targetnode a = m`
  have "V \<in> set (ParamDefs (targetnode a))" by(fastforce simp:set_conv_nth)
  with `n = Actual_out (m, x)` `targetnode a = m` `valid_edge a`
  show ?case by(fastforce intro:ParamDefs_in_Def)
qed



definition data_dependence :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
("_ influences _ in _" [51,0,0])
  where "n influences V in n' \<equiv> \<exists>as. (V \<in> Def\<^bsub>SDG\<^esub> n) \<and> (V \<in> Use\<^bsub>SDG\<^esub> n') \<and> 
  (parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n') \<and>
  (\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (tl as))
         \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n'')"


subsection {* Control dependence *}

definition control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ controls _" [51,0])
where "n controls n' \<equiv> \<exists>a a' as. n -a#as\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set(sourcenodes (a#as)) \<and>
    intra_kind(kind a) \<and> n' postdominates (targetnode a) \<and> 
    valid_edge a' \<and> intra_kind(kind a') \<and> sourcenode a' = n \<and> 
    \<not> n' postdominates (targetnode a')"


lemma control_dependence_path:
  assumes "n controls n'" obtains as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "as \<noteq> []"
using `n controls n'`
by(fastforce simp:control_dependence_def)


lemma Exit_does_not_control [dest]:
  assumes "(_Exit_) controls n'" shows "False"
proof -
  from `(_Exit_) controls n'` obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by(auto simp:control_dependence_def)
  thus ?thesis by(rule Exit_source)
qed


lemma Exit_not_control_dependent: 
  assumes "n controls n'" shows "n' \<noteq> (_Exit_)"
proof -
  from `n controls n'` obtain a as where "n -a#as\<rightarrow>\<^sub>\<iota>* n'"
    and "n' postdominates (targetnode a)"
    by(auto simp:control_dependence_def)
  from `n -a#as\<rightarrow>\<^sub>\<iota>* n'` have "valid_edge a" 
    by(fastforce elim:path.cases simp:intra_path_def)
  hence "valid_node (targetnode a)" by simp
  with `n' postdominates (targetnode a)` `n -a#as\<rightarrow>\<^sub>\<iota>* n'` show ?thesis
    by(fastforce elim:Exit_no_postdominator)
qed


lemma which_node_intra_standard_control_dependence_source:
  assumes "nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n" and "sourcenode a = n'" and "sourcenode a' = n'"
  and "n \<notin> set(sourcenodes (a#as'))" and "valid_edge a'" and "intra_kind(kind a')"
  and "inner_node n" and "\<not> method_exit n" and "\<not> n postdominates (targetnode a')"
  and last:"\<forall>ax ax'. ax \<in> set as' \<and> sourcenode ax = sourcenode ax' \<and>
    valid_edge ax' \<and> intra_kind(kind ax') \<longrightarrow> n postdominates targetnode ax'"
  shows "n' controls n"
proof -
  from `nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n` `sourcenode a = n'` have "n' -a#as'\<rightarrow>\<^sub>\<iota>* n"
    by(fastforce dest:path_split_second simp:intra_path_def)
  from `nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n` have "valid_edge a"
    by(fastforce intro:path_split simp:intra_path_def)
  show ?thesis
  proof(cases "n postdominates (targetnode a)")
    case True
    with `n' -a#as'\<rightarrow>\<^sub>\<iota>* n` `n \<notin> set(sourcenodes (a#as'))`
      `valid_edge a'` `intra_kind(kind a')` `sourcenode a' = n'` 
      `\<not> n postdominates (targetnode a')` show ?thesis
      by(fastforce simp:control_dependence_def intra_path_def)
  next
    case False
    show ?thesis
    proof(cases "as' = []")
      case True
      with `n' -a#as'\<rightarrow>\<^sub>\<iota>* n` have "targetnode a = n" 
        by(fastforce elim:path.cases simp:intra_path_def)
      with `inner_node n` `\<not> method_exit n` have "n postdominates (targetnode a)"
        by(fastforce dest:inner_is_valid intro:postdominate_refl)
      with `\<not> n postdominates (targetnode a)` show ?thesis by simp
    next
      case False
      with `nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n` have "targetnode a -as'\<rightarrow>\<^sub>\<iota>* n"
        by(fastforce intro:path_split simp:intra_path_def)
     with `\<not> n postdominates (targetnode a)` `valid_edge a` `inner_node n`
        `targetnode a -as'\<rightarrow>\<^sub>\<iota>* n`
      obtain asx pex where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        and "n \<notin> set (sourcenodes asx)"
        by(fastforce dest:inner_is_valid simp:postdominate_def)
      show ?thesis
      proof(cases "\<exists>asx'. asx = as'@asx'")
        case True
        then obtain asx' where [simp]:"asx = as'@asx'" by blast
        from `targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex` `targetnode a -as'\<rightarrow>\<^sub>\<iota>* n`
          `as' \<noteq> []` `method_exit pex` `\<not> method_exit n`
        obtain a'' as'' where "asx' = a''#as'' \<and> sourcenode a'' = n"
          by(cases asx')(auto dest:path_split path_det simp:intra_path_def)
        hence "n \<in> set(sourcenodes asx)" by(simp add:sourcenodes_def)
        with `n \<notin> set (sourcenodes asx)` have False by simp
        thus ?thesis by simp
      next
        case False
        hence "\<forall>asx'. asx \<noteq> as'@asx'" by simp
        then obtain j asx' where "asx = (take j as')@asx'"
          and "j < length as'" and "\<forall>k > j. \<forall>asx''. asx \<noteq> (take k as')@asx''"
          by(auto elim:path_split_general)
        from `asx = (take j as')@asx'` `j < length as'`
        have "\<exists>as'1 as'2. asx = as'1@asx' \<and> 
          as' = as'1@as'2 \<and> as'2 \<noteq> [] \<and> as'1 = take j as'"
          by simp(rule_tac x= "drop j as'" in exI,simp)
        then obtain as'1 as'' where "asx = as'1@asx'"
          and "as'1 = take j as'"
          and "as' = as'1@as''" and "as'' \<noteq> []" by blast
        from `as' = as'1@as''` `as'' \<noteq> []` obtain a1 as'2 
          where "as' = as'1@a1#as'2" and "as'' = a1#as'2"
          by(cases as'') auto
        have "asx' \<noteq> []"
        proof(cases "asx' = []")
          case True
          with `asx = as'1@asx'` `as' = as'1@as''` `as'' = a1#as'2`
          have "as' = asx@a1#as'2" by simp
          with `n' -a#as'\<rightarrow>\<^sub>\<iota>* n` have "n' -(a#asx)@a1#as'2\<rightarrow>\<^sub>\<iota>* n" by simp
          hence "n' -(a#asx)@a1#as'2\<rightarrow>* n" 
            and "\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)"
            by(simp_all add:intra_path_def)
          from `n' -(a#asx)@a1#as'2\<rightarrow>* n`
          have "n' -a#asx\<rightarrow>* sourcenode a1" and "valid_edge a1"
            by -(erule path_split)+
          from `\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)` 
          have "\<forall>ax \<in> set(a#asx). intra_kind(kind ax)" by simp
          with `n' -a#asx\<rightarrow>* sourcenode a1` have "n' -a#asx\<rightarrow>\<^sub>\<iota>* sourcenode a1"
            by(simp add:intra_path_def)
          hence "targetnode a -asx\<rightarrow>\<^sub>\<iota>* sourcenode a1"
            by(fastforce intro:path_split_Cons simp:intra_path_def)
          with `targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex` have "pex = sourcenode a1"
            by(fastforce intro:path_det simp:intra_path_def)
          from `\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)`
          have "intra_kind (kind a1)" by simp
          from `method_exit pex` have False
          proof(rule method_exit_cases)
            assume "pex = (_Exit_)"
            with `pex = sourcenode a1` have "sourcenode a1 = (_Exit_)" by simp
            with `valid_edge a1` show False by(rule Exit_source)
          next
            fix a Q f p assume "pex = sourcenode a" and "valid_edge a"
              and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `pex = sourcenode a` 
              `pex = sourcenode a1` `valid_edge a1` `intra_kind (kind a1)`
            show False by(fastforce dest:return_edges_only simp:intra_kind_def)
          qed
          thus ?thesis by simp
        qed simp
        with `asx = as'1@asx'` obtain a2 asx'1 
          where "asx = as'1@a2#asx'1"
          and "asx' = a2#asx'1" by(cases asx') auto
        from `n' -a#as'\<rightarrow>\<^sub>\<iota>* n` `as' = as'1@a1#as'2` 
        have "n' -(a#as'1)@a1#as'2\<rightarrow>\<^sub>\<iota>* n" by simp
        hence "n' -(a#as'1)@a1#as'2\<rightarrow>* n" 
          and "\<forall>ax \<in> set((a#as'1)@a1#as'2). intra_kind(kind ax)"
          by(simp_all add: intra_path_def)
        from `n' -(a#as'1)@a1#as'2\<rightarrow>* n` have "n' -a#as'1\<rightarrow>* sourcenode a1"
          and "valid_edge a1" by -(erule path_split)+
        from `\<forall>ax \<in> set((a#as'1)@a1#as'2). intra_kind(kind ax)`
        have "\<forall>ax \<in> set(a#as'1). intra_kind(kind ax)" by simp
        with `n' -a#as'1\<rightarrow>* sourcenode a1` have "n' -a#as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1"
          by(simp add:intra_path_def)
        hence "targetnode a -as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1"
          by(fastforce intro:path_split_Cons simp:intra_path_def)
        from `targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex` `asx = as'1@a2#asx'1`
        have "targetnode a -as'1@a2#asx'1\<rightarrow>* pex" by(simp add:intra_path_def)
        hence "targetnode a -as'1\<rightarrow>* sourcenode a2" and "valid_edge a2"
          and "targetnode a2 -asx'1\<rightarrow>* pex" by(auto intro:path_split)
        from `targetnode a2 -asx'1\<rightarrow>* pex` `asx = as'1@a2#asx'1`
          `targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex`
        have "targetnode a2 -asx'1\<rightarrow>\<^sub>\<iota>* pex" by(simp add:intra_path_def)
        from `targetnode a -as'1\<rightarrow>* sourcenode a2` 
          `targetnode a -as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1` 
        have "sourcenode a1 = sourcenode a2"
          by(fastforce intro:path_det simp:intra_path_def)
        from `asx = as'1@a2#asx'1` `n \<notin> set (sourcenodes asx)`
        have "n \<notin> set (sourcenodes asx'1)" by(simp add:sourcenodes_def)
        with `targetnode a2 -asx'1\<rightarrow>\<^sub>\<iota>* pex` `method_exit pex`
          `asx = as'1@a2#asx'1`
        have "\<not> n postdominates targetnode a2" by(fastforce simp:postdominate_def)
        from `asx = as'1@a2#asx'1` `targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex`
        have "intra_kind (kind a2)" by(simp add:intra_path_def)
        from `as' = as'1@a1#as'2` have "a1 \<in> set as'" by simp
        with `sourcenode a1 = sourcenode a2` last `valid_edge a2` 
          `intra_kind (kind a2)`
        have "n postdominates targetnode a2" by blast
        with `\<not> n postdominates targetnode a2` have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed



subsection {* SDG without summary edges *}


inductive cdep_edge :: "'node SDG_node \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ \<longrightarrow>\<^bsub>cd\<^esub> _" [51,0] 80)
  and ddep_edge :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_\<rightarrow>\<^bsub>dd\<^esub> _" [51,0,0] 80)
  and call_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ -_\<rightarrow>\<^bsub>call\<^esub> _" [51,0,0] 80)
  and return_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ -_\<rightarrow>\<^bsub>ret\<^esub> _" [51,0,0] 80)
  and param_in_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_:_\<rightarrow>\<^bsub>in\<^esub> _" [51,0,0,0] 80)
  and param_out_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_:_\<rightarrow>\<^bsub>out\<^esub> _" [51,0,0,0] 80)
  and SDG_edge :: "'node SDG_node \<Rightarrow> 'var option \<Rightarrow> 
                          ('pname \<times> bool) option \<Rightarrow> 'node SDG_node \<Rightarrow> bool"

where
    (* Syntax *)
  "n \<longrightarrow>\<^bsub>cd\<^esub> n' == SDG_edge n None None n'"
  | "n -V\<rightarrow>\<^bsub>dd\<^esub> n' == SDG_edge n (Some V) None n'"
  | "n -p\<rightarrow>\<^bsub>call\<^esub> n' == SDG_edge n None (Some(p,True)) n'"
  | "n -p\<rightarrow>\<^bsub>ret\<^esub> n' == SDG_edge n None (Some(p,False)) n'"
  | "n -p:V\<rightarrow>\<^bsub>in\<^esub> n' == SDG_edge n (Some V) (Some(p,True)) n'"
  | "n -p:V\<rightarrow>\<^bsub>out\<^esub> n' == SDG_edge n (Some V) (Some(p,False)) n'"

    (* Rules *)
  | SDG_cdep_edge:
    "\<lbrakk>n = CFG_node m; n' = CFG_node m'; m controls m'\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_proc_entry_exit_cdep:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (targetnode a);
      a' \<in> get_return_edges a; n' = CFG_node (sourcenode a')\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_parent_cdep_edge:
    "\<lbrakk>valid_SDG_node n'; m = parent_node n'; n = CFG_node m; n \<noteq> n'\<rbrakk> 
      \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_ddep_edge:"n influences V in n' \<Longrightarrow> n -V\<rightarrow>\<^bsub>dd\<^esub> n'"
  | SDG_call_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n -p\<rightarrow>\<^bsub>call\<^esub> n'"
  | SDG_return_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n -p\<rightarrow>\<^bsub>ret\<^esub> n'"
  | SDG_param_in_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs; V = ins!x;
      x < length ins; n = Actual_in (sourcenode a,x); n' = Formal_in (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n -p:V\<rightarrow>\<^bsub>in\<^esub> n'"
  | SDG_param_out_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs; V = outs!x;
      x < length outs; n = Formal_out (sourcenode a,x); 
      n' = Actual_out (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n -p:V\<rightarrow>\<^bsub>out\<^esub> n'"


lemma cdep_edge_cases:
  "\<lbrakk>n \<longrightarrow>\<^bsub>cd\<^esub> n'; (parent_node n) controls (parent_node n') \<Longrightarrow> P;
    \<And>a Q r p fs a'. \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
                  parent_node n = targetnode a; parent_node n' = sourcenode a'\<rbrakk> \<Longrightarrow> P;
    \<And>m. \<lbrakk>n = CFG_node m; m = parent_node n'; n \<noteq> n'\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by -(erule SDG_edge.cases,auto)


lemma SDG_edge_valid_SDG_node:
  assumes "SDG_edge n Vopt popt n'" 
  shows "valid_SDG_node n" and "valid_SDG_node n'"
using `SDG_edge n Vopt popt n'`
proof(induct rule:SDG_edge.induct)
  case (SDG_cdep_edge n m n' m') 
  thus "valid_SDG_node n" "valid_SDG_node n'"
    by(fastforce elim:control_dependence_path elim:path_valid_node 
                simp:intra_path_def)+
next
  case (SDG_proc_entry_exit_cdep a Q r p f n a' n') case 1
  from `valid_edge a` `n = CFG_node (targetnode a)` show ?case by simp
next
  case (SDG_proc_entry_exit_cdep a Q r p f n a' n') case 2
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
    by(rule get_return_edges_valid)
  with `n' = CFG_node (sourcenode a')` show ?case by simp
next
  case (SDG_ddep_edge n V n')
  thus "valid_SDG_node n" "valid_SDG_node n'" 
    by(auto intro:in_Use_valid_SDG_node in_Def_valid_SDG_node
             simp:data_dependence_def)
qed(fastforce intro:valid_SDG_CFG_node)+


lemma valid_SDG_node_cases: 
  assumes "valid_SDG_node n"
  shows "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
proof(cases n)
  case (CFG_node m) thus ?thesis by simp
next
  case (Formal_in z)
  from `n = Formal_in z` obtain m x where "z = (m,x)" by(cases z) auto
  with `valid_SDG_node n` `n = Formal_in z` have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Formal_out z)
  from `n = Formal_out z` obtain m x where "z = (m,x)" by(cases z) auto
  with `valid_SDG_node n` `n = Formal_out z` have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Actual_in z)
  from `n = Actual_in z` obtain m x where "z = (m,x)" by(cases z) auto
  with `valid_SDG_node n` `n = Actual_in z` have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Actual_out z)
  from `n = Actual_out z` obtain m x where "z = (m,x)" by(cases z) auto
  with `valid_SDG_node n` `n = Actual_out z` have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
qed


lemma SDG_cdep_edge_CFG_node: "n \<longrightarrow>\<^bsub>cd\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"None::('pname \<times> bool) option" n' 
   rule:SDG_edge.induct) auto

lemma SDG_call_edge_CFG_node: "n -p\<rightarrow>\<^bsub>call\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"Some(p,True)" n' 
   rule:SDG_edge.induct) auto

lemma SDG_return_edge_CFG_node: "n -p\<rightarrow>\<^bsub>ret\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"Some(p,False)" n' 
   rule:SDG_edge.induct) auto



lemma SDG_call_or_param_in_edge_unique_CFG_call_edge:
  "SDG_edge n Vopt (Some(p,True)) n'
  \<Longrightarrow> \<exists>!a. valid_edge a \<and> sourcenode a = parent_node n \<and> 
          targetnode a = parent_node n' \<and> (\<exists>Q r fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
proof(induct n Vopt "Some(p,True)" n' rule:SDG_edge.induct)
  case (SDG_call_edge a Q r fs n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from `sourcenode a' = parent_node n` `n = CFG_node (sourcenode a)`
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from `targetnode a' = parent_node n'` `n' = CFG_node (targetnode a)`
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using `valid_edge a'` `valid_edge a`
      by(fastforce intro:edge_det) }
  with `valid_edge a` `n = CFG_node (sourcenode a)` `n' = CFG_node (targetnode a)`
    `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` show ?case by(fastforce intro!:ex1I[of _ a])
next
  case (SDG_param_in_edge a Q r fs ins outs V x n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from `sourcenode a' = parent_node n` `n = Actual_in (sourcenode a,x)`
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from `targetnode a' = parent_node n'` `n' = Formal_in (targetnode a,x)`
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using `valid_edge a'` `valid_edge a`
      by(fastforce intro:edge_det) }
  with `valid_edge a` `n = Actual_in (sourcenode a,x)` 
    `n' = Formal_in (targetnode a,x)` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  show ?case by(fastforce intro!:ex1I[of _ a])
qed simp_all


lemma SDG_return_or_param_out_edge_unique_CFG_return_edge:
  "SDG_edge n Vopt (Some(p,False)) n'
  \<Longrightarrow> \<exists>!a. valid_edge a \<and> sourcenode a = parent_node n \<and> 
          targetnode a = parent_node n' \<and> (\<exists>Q f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
proof(induct n Vopt "Some(p,False)" n' rule:SDG_edge.induct)
  case (SDG_return_edge a Q f n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n" 
      and "targetnode a' = parent_node n'"
    from `sourcenode a' = parent_node n` `n = CFG_node (sourcenode a)`
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from `targetnode a' = parent_node n'` `n' = CFG_node (targetnode a)`
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using `valid_edge a'` `valid_edge a`
      by(fastforce intro:edge_det) }
  with `valid_edge a` `n = CFG_node (sourcenode a)` `n' = CFG_node (targetnode a)`
    `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show ?case by(fastforce intro!:ex1I[of _ a])
next
  case (SDG_param_out_edge a Q f ins outs V x n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from `sourcenode a' = parent_node n` `n = Formal_out (sourcenode a,x)`
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from `targetnode a' = parent_node n'` `n' = Actual_out (targetnode a,x)`
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using `valid_edge a'` `valid_edge a`
      by(fastforce intro:edge_det) }
  with `valid_edge a` `n = Formal_out (sourcenode a,x)`
    `n' = Actual_out (targetnode a,x)` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
  show ?case by(fastforce intro!:ex1I[of _ a])
qed simp_all


lemma Exit_no_SDG_edge_source:
  "SDG_edge (CFG_node (_Exit_)) Vopt popt n' \<Longrightarrow> False"
proof(induct "CFG_node (_Exit_)" Vopt popt n' rule:SDG_edge.induct)
  case (SDG_cdep_edge m n' m')
  hence "(_Exit_) controls m'" by simp
  thus ?case by fastforce
next
  case (SDG_proc_entry_exit_cdep a Q r p fs a' n')
  from `CFG_node (_Exit_) = CFG_node (targetnode a)`
  have "targetnode a = (_Exit_)" by simp
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with `targetnode a = (_Exit_)` have "p = Main"
    by(auto simp:get_proc_Exit)
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have False
    by(fastforce intro:Main_no_call_target)
  thus ?thesis by simp
next
  case (SDG_parent_cdep_edge n' m)
  from `CFG_node (_Exit_) = CFG_node m` 
  have [simp]:"m = (_Exit_)" by simp
  with `valid_SDG_node n'` `m = parent_node n'` `CFG_node (_Exit_) \<noteq> n'`
  have False by -(drule valid_SDG_node_parent_Exit,simp+)
  thus ?thesis by simp
next
  case (SDG_ddep_edge V n')
  hence "(CFG_node (_Exit_)) influences V in n'" by simp
  with Exit_empty show ?case
    by(fastforce dest:path_Exit_source SDG_Def_parent_Def 
                simp:data_dependence_def intra_path_def)
next
  case (SDG_call_edge a Q r p fs n')
  from `CFG_node (_Exit_) = CFG_node (sourcenode a)`
  have "sourcenode a = (_Exit_)" by simp
  with `valid_edge a` show ?case by(rule Exit_source)
next
  case (SDG_return_edge a Q p f n')
  from `CFG_node (_Exit_) = CFG_node (sourcenode a)`
  have "sourcenode a = (_Exit_)" by simp
  with `valid_edge a` show ?case by(rule Exit_source)
qed simp_all


subsection {* Intraprocedural paths in the SDG *}

inductive intra_SDG_path :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ i-_\<rightarrow>\<^sub>d* _" [51,0,0] 80) 

where iSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n i-[]\<rightarrow>\<^sub>d* n"

  | iSp_Append_cdep:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n i-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | iSp_Append_ddep:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n''; n'' -V\<rightarrow>\<^bsub>dd\<^esub> n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n i-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma intra_SDG_path_Append:
  "\<lbrakk>n'' i-ns'\<rightarrow>\<^sub>d* n'; n i-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n i-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_SDG_path.induct,
   auto intro:intra_SDG_path.intros simp:append_assoc[THEN sym] simp del:append_assoc)


lemma intra_SDG_path_valid_SDG_node:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using `n i-ns\<rightarrow>\<^sub>d* n'`
by(induct rule:intra_SDG_path.induct,
   auto intro:SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma intra_SDG_path_intra_CFG_path:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from `n i-ns\<rightarrow>\<^sub>d* n'`
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_SDG_path.induct)
    case (iSp_Nil n)
    from `valid_SDG_node n` have "valid_node (parent_node n)"
      by(rule valid_SDG_CFG_node)
    hence "parent_node n -[]\<rightarrow>* parent_node n" by(rule empty_path)
    thus ?case by(auto simp:intra_path_def)
  next
    case (iSp_Append_cdep n ns n'' n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from `n'' \<longrightarrow>\<^bsub>cd\<^esub> n'` show ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with `parent_node n'' = targetnode a` `parent_node n' = sourcenode a'` 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` show ?thesis by fastforce
    qed
  next
    case (iSp_Append_ddep n ns n'' V n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast 
    from `n'' -V\<rightarrow>\<^bsub>dd\<^esub> n'` have "n'' influences V in n'"
      by(fastforce elim:SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  qed
qed


subsection {* Control dependence paths in the SDG *}

inductive cdep_SDG_path :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ cd-_\<rightarrow>\<^sub>d* _" [51,0,0] 80) 

where cdSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n cd-[]\<rightarrow>\<^sub>d* n"

  | cdSp_Append_cdep:
  "\<lbrakk>n cd-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n cd-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma cdep_SDG_path_intra_SDG_path:
  "n cd-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n i-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:cdep_SDG_path.induct,auto intro:intra_SDG_path.intros)


lemma Entry_cdep_SDG_path:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'" and "inner_node n'" and "\<not> method_exit n'"
  obtains ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n'"
  and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
proof(atomize_elim)
  from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'` `inner_node n'` `\<not> method_exit n'`
  show "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
    (\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as))"
  proof(induct as arbitrary:n' rule:length_induct)
    fix as n'
    assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
      (\<forall>n''. (_Entry_) -as'\<rightarrow>\<^sub>\<iota>* n'' \<longrightarrow> inner_node n'' \<longrightarrow> \<not> method_exit n'' \<longrightarrow>
        (\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n'' \<and> ns \<noteq> [] \<and>
              (\<forall>nx\<in>set ns. parent_node nx \<in> set (sourcenodes as'))))"
      and "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'" and "inner_node n'" and "\<not> method_exit n'"
    thus "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
      (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
    proof -
      have "\<exists>ax asx zs. (_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set (sourcenodes (ax#asx)) \<and> 
                        as = (ax#asx)@zs"
      proof(cases "n' \<in> set (sourcenodes as)")
        case True
        hence "\<exists>n'' \<in> set(sourcenodes as). n' = n''" by simp
        then obtain ns' ns'' where "sourcenodes as = ns'@n'#ns''"
          and "\<forall>n'' \<in> set ns'. n' \<noteq> n''"
          by(fastforce elim!:split_list_first_propE)
        from `sourcenodes as = ns'@n'#ns''` obtain xs ys ax
          where "sourcenodes xs = ns'" and "as = xs@ax#ys"
          and "sourcenode ax = n'"
          by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
        from `\<forall>n'' \<in> set ns'. n' \<noteq> n''` `sourcenodes xs = ns'`
        have "n' \<notin> set(sourcenodes xs)" by fastforce
        from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'` `as = xs@ax#ys` have "(_Entry_) -xs@ax#ys\<rightarrow>\<^sub>\<iota>* n'"
          by simp
        with `sourcenode ax = n'` have "(_Entry_) -xs\<rightarrow>\<^sub>\<iota>* n'" 
          by(fastforce dest:path_split simp:intra_path_def)
        with `inner_node n'` have "xs \<noteq> []"
          by(fastforce elim:path.cases simp:intra_path_def)
        with `n' \<notin> set(sourcenodes xs)` `(_Entry_) -xs\<rightarrow>\<^sub>\<iota>* n'` `as = xs@ax#ys`
        show ?thesis by(cases xs) auto
      next
        case False
        with `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'` `inner_node n'`
        show ?thesis by(cases as)(auto elim:path.cases simp:intra_path_def)
      qed
      then obtain ax asx zs where "(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'" 
        and "n' \<notin> set (sourcenodes (ax#asx))" and "as = (ax#asx)@zs" by blast
      show ?thesis
      proof(cases "\<forall>a' a''. a' \<in> set asx \<and> sourcenode a' = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<longrightarrow> n' postdominates targetnode a''")
        case True
        have "(_Exit_) -[]\<rightarrow>\<^sub>\<iota>* (_Exit_)" 
          by(fastforce intro:empty_path simp:intra_path_def)
        hence "\<not> n' postdominates (_Exit_)"
          by(fastforce simp:postdominate_def sourcenodes_def method_exit_def)
        from `(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'` have "(_Entry_) -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'" by simp
        from `(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'` have [simp]:"sourcenode ax = (_Entry_)" 
          and "valid_edge ax"
          by(auto intro:path_split_Cons simp:intra_path_def)
        from Entry_Exit_edge obtain a' where "sourcenode a' = (_Entry_)"
          and "targetnode a' = (_Exit_)" and "valid_edge a'" 
          and "intra_kind(kind a')" by(auto simp:intra_kind_def)
        with `(_Entry_) -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'` `\<not> n' postdominates (_Exit_)`
          `valid_edge ax` True `sourcenode ax = (_Entry_)` 
          `n' \<notin> set (sourcenodes (ax#asx))` `inner_node n'` `\<not> method_exit n'`
        have "sourcenode ax controls n'"
          by -(erule which_node_intra_standard_control_dependence_source
                     [of _ _ _ _ _ _ a'],auto)
        hence "CFG_node (_Entry_) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
          by(fastforce intro:SDG_cdep_edge)
        hence "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* CFG_node n'"
          by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
        moreover
        from `as = (ax#asx)@zs` have "(_Entry_) \<in> set(sourcenodes as)"
          by(simp add:sourcenodes_def)
        ultimately show ?thesis by fastforce
      next
        case False
        hence "\<exists>a' \<in> set asx. \<exists>a''. sourcenode a' = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a''"
          by fastforce
        then obtain ax' asx' asx'' where "asx = asx'@ax'#asx'' \<and>
          (\<exists>a''. sourcenode ax' = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'') \<and>
          (\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a''))"
          by(blast elim!:split_list_last_propE)
        then obtain ai where "asx = asx'@ax'#asx''"
          and "sourcenode ax' = sourcenode ai"
          and "valid_edge ai" and "intra_kind(kind ai)"
          and "\<not> n' postdominates targetnode ai"
          and "\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'')"
          by blast
        from `(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'` `asx = asx'@ax'#asx''`
        have "(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'" by simp
        from `n' \<notin> set (sourcenodes (ax#asx))` `asx = asx'@ax'#asx''`
        have "n' \<notin> set (sourcenodes (ax'#asx''))"
          by(auto simp:sourcenodes_def)
        with `inner_node n'` `\<not> n' postdominates targetnode ai`
          `n' \<notin> set (sourcenodes (ax'#asx''))` `sourcenode ax' = sourcenode ai`
          `\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'')`
          `valid_edge ai` `intra_kind(kind ai)` `\<not> method_exit n'`
          `(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'`
        have "sourcenode ax' controls n'"
          by(fastforce intro!:which_node_intra_standard_control_dependence_source)
        hence "CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
          by(fastforce intro:SDG_cdep_edge)
        from `(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'`
        have "(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'" and "valid_edge ax'"
          by(auto intro:path_split simp:intra_path_def simp del:append_Cons)
        from `asx = asx'@ax'#asx''` `as = (ax#asx)@zs`
        have "length (ax#asx') < length as" by simp
        from `valid_edge ax'` have "valid_node (sourcenode ax')" by simp
        hence "inner_node (sourcenode ax')"
        proof(cases "sourcenode ax'" rule:valid_node_cases)
          case Entry 
          with `(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'`
          have "(_Entry_) -ax#asx'\<rightarrow>* (_Entry_)" by(simp add:intra_path_def)
          hence False by(fastforce dest:path_Entry_target)
          thus ?thesis by simp
        next
          case Exit
          with `valid_edge ax'` have False by(rule Exit_source)
          thus ?thesis by simp
        qed simp
        from `asx = asx'@ax'#asx''` `(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'`
        have "intra_kind (kind ax')" by(simp add:intra_path_def)
        have "\<not> method_exit (sourcenode ax')"
        proof
          assume "method_exit (sourcenode ax')"
          thus False
          proof(rule method_exit_cases)
            assume "sourcenode ax' = (_Exit_)"
            with `valid_edge ax'` show False by(rule Exit_source)
          next
            fix x Q f p assume " sourcenode ax' = sourcenode x"
              and "valid_edge x" and "kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from `valid_edge x` `kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `sourcenode ax' = sourcenode x`
            `valid_edge ax'` `intra_kind (kind ax')` show False
              by(fastforce dest:return_edges_only simp:intra_kind_def)
          qed
        qed
        with IH `length (ax#asx') < length as` `(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'`
          `inner_node (sourcenode ax')`
        obtain ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
          and "ns \<noteq> []" 
          and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes (ax#asx'))"
          by blast
        from `CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')`
          `CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'`
        have "CFG_node (_Entry_) cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'"
          by(fastforce intro:cdSp_Append_cdep)
        from `as = (ax#asx)@zs` `asx = asx'@ax'#asx''`
        have "sourcenode ax' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def)
        with `\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes (ax#asx'))`
          `as = (ax#asx)@zs` `asx = asx'@ax'#asx''`
        have "\<forall>n'' \<in> set (ns@[CFG_node (sourcenode ax')]).
          parent_node n'' \<in> set(sourcenodes as)"
          by(fastforce simp:sourcenodes_def)
        with `CFG_node (_Entry_) cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'`
        show ?thesis by fastforce
      qed
    qed
  qed
qed


lemma in_proc_cdep_SDG_path:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n \<noteq> n'" and "n' \<noteq> (_Exit_)" and "valid_edge a"
  and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = n"
  obtains ns where "CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n'"
  and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
proof(atomize_elim)
  show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and>
             ns \<noteq> [] \<and> (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
  proof(cases "\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> 
                    ax \<notin> get_return_edges a")
    case True
    from `n -as\<rightarrow>\<^sub>\<iota>* n'` `n \<noteq> n'` `n' \<noteq> (_Exit_)`
      `\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a`
    show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
      (\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as))"
    proof(induct as arbitrary:n' rule:length_induct)
      fix as n'
      assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
        (\<forall>n''. n -as'\<rightarrow>\<^sub>\<iota>* n'' \<longrightarrow> n \<noteq> n'' \<longrightarrow> n'' \<noteq> (_Exit_) \<longrightarrow>
          (\<forall>ax. valid_edge ax \<and> sourcenode ax = n'' \<longrightarrow> ax \<notin> get_return_edges a) \<longrightarrow>
            (\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n'' \<and> ns \<noteq> [] \<and>
                  (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as'))))"
        and "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n \<noteq> n'" and "n' \<noteq> (_Exit_)"
        and "\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a"
      show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
                 (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
      proof(cases "method_exit n'")
        case True
        thus ?thesis
        proof(rule method_exit_cases)
          assume "n' = (_Exit_)"
          with `n' \<noteq> (_Exit_)` have False by simp
          thus ?thesis by simp
        next
          fix a' Q' f' p'
          assume "n' = sourcenode a'" and "valid_edge a'" and "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'"
          from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc(targetnode a) = p"
            by(rule get_proc_call)
          from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "get_proc n = get_proc n'" 
            by(rule intra_path_get_procs)
          with `get_proc(targetnode a) = p` `targetnode a = n`
          have "get_proc (targetnode a) = get_proc n'" by simp
          from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'`
          have "get_proc (sourcenode a') = p'" by(rule get_proc_return)
          with `n' = sourcenode a'` `get_proc (targetnode a) = get_proc n'` 
            `get_proc (targetnode a) = p` have "p = p'" by simp
          with `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'`
          obtain ax where "valid_edge ax" and "\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            and "a' \<in> get_return_edges ax" by(auto dest:return_needs_call)
          hence "CFG_node (targetnode ax) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')"
            by(fastforce intro:SDG_proc_entry_exit_cdep)
          with `valid_edge ax` 
          have "CFG_node (targetnode ax) cd-[]@[CFG_node (targetnode ax)]\<rightarrow>\<^sub>d* 
            CFG_node (sourcenode a')"
            by(fastforce intro:cdep_SDG_path.intros)
          from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge ax` 
            `\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "targetnode a = targetnode ax"
            by(fastforce intro:same_proc_call_unique_target)
          from `n -as\<rightarrow>\<^sub>\<iota>* n'` `n \<noteq> n'`
          have "as \<noteq> []" by(fastforce elim:path.cases simp:intra_path_def)
          with `n -as\<rightarrow>\<^sub>\<iota>* n'` have "hd (sourcenodes as) = n"
            by(fastforce intro:path_sourcenode simp:intra_path_def)
          moreover
          from `as \<noteq> []` have "hd (sourcenodes as) \<in> set (sourcenodes as)"
            by(fastforce intro:hd_in_set simp:sourcenodes_def)
          ultimately have "n \<in> set (sourcenodes as)" by simp
          with `n' = sourcenode a'` `targetnode a = targetnode ax`
            `targetnode a = n`
            `CFG_node (targetnode ax) cd-[]@[CFG_node (targetnode ax)]\<rightarrow>\<^sub>d* 
            CFG_node (sourcenode a')`
          show ?thesis by fastforce
        qed
      next
        case False
        from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain a' 
          where "a' \<in> get_return_edges a"
          by(fastforce dest:get_return_edge_call)
        with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
          by(fastforce dest!:call_return_edges)
        with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a` obtain a''
          where "valid_edge a''" and "sourcenode a'' = targetnode a" 
          and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
          by -(drule intra_proc_additional_edge,auto)
        from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
          by(rule get_return_edges_valid)
        have "\<exists>ax asx zs. n -ax#asx\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set (sourcenodes (ax#asx)) \<and> 
                          as = (ax#asx)@zs"
        proof(cases "n' \<in> set (sourcenodes as)")
          case True
          hence "\<exists>n'' \<in> set(sourcenodes as). n' = n''" by simp
          then obtain ns' ns'' where "sourcenodes as = ns'@n'#ns''"
            and "\<forall>n'' \<in> set ns'. n' \<noteq> n''"
            by(fastforce elim!:split_list_first_propE)
          from `sourcenodes as = ns'@n'#ns''` obtain xs ys ax
            where "sourcenodes xs = ns'" and "as = xs@ax#ys"
            and "sourcenode ax = n'"
            by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
          from `\<forall>n'' \<in> set ns'. n' \<noteq> n''` `sourcenodes xs = ns'`
          have "n' \<notin> set(sourcenodes xs)" by fastforce
          from `n -as\<rightarrow>\<^sub>\<iota>* n'` `as = xs@ax#ys` have "n -xs@ax#ys\<rightarrow>\<^sub>\<iota>* n'" by simp
          with `sourcenode ax = n'` have "n -xs\<rightarrow>\<^sub>\<iota>* n'" 
            by(fastforce dest:path_split simp:intra_path_def)
          with `n \<noteq> n'` have "xs \<noteq> []" by(fastforce simp:intra_path_def)
          with `n' \<notin> set(sourcenodes xs)` `n -xs\<rightarrow>\<^sub>\<iota>* n'` `as = xs@ax#ys` show ?thesis
            by(cases xs) auto
        next
          case False
          with `n -as\<rightarrow>\<^sub>\<iota>* n'` `n \<noteq> n'` 
          show ?thesis by(cases as)(auto simp:intra_path_def)
        qed
        then obtain ax asx zs where "n -ax#asx\<rightarrow>\<^sub>\<iota>* n'" 
          and "n' \<notin> set (sourcenodes (ax#asx))" and "as = (ax#asx)@zs" by blast
        from `n -ax#asx\<rightarrow>\<^sub>\<iota>* n'` `n' \<noteq> (_Exit_)` have "inner_node n'"
          by(fastforce intro:path_valid_node simp:inner_node_def intra_path_def)
        from `valid_edge a` `targetnode a = n` have "valid_node n" by fastforce
        show ?thesis
        proof(cases "\<forall>a' a''. a' \<in> set asx \<and> sourcenode a' = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<longrightarrow> 
            n' postdominates targetnode a''")
          case True
          from `targetnode a = n` `sourcenode a'' = targetnode a` 
            `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>`
          have "sourcenode a'' = n" and "intra_kind(kind a'')"
            by(auto simp:intra_kind_def)
          { fix as' assume "targetnode a'' -as'\<rightarrow>\<^sub>\<iota>* n'"
            from `valid_edge a'` `targetnode a'' = sourcenode a'` 
              `a' \<in> get_return_edges a` 
              `\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a`
            have "targetnode a'' \<noteq> n'" by fastforce
            with `targetnode a'' -as'\<rightarrow>\<^sub>\<iota>* n'` obtain ax' where "valid_edge ax'"
              and "targetnode a'' = sourcenode ax'" and "intra_kind(kind ax')"
              by(clarsimp simp:intra_path_def)(erule path.cases,fastforce+)
            from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `valid_edge ax'`
              `targetnode a'' = sourcenode a'` `targetnode a'' = sourcenode ax'`
              `intra_kind(kind ax')`
            have False by(fastforce dest:return_edges_only simp:intra_kind_def) }
          hence "\<not> n' postdominates targetnode a''"
            by(fastforce elim:postdominate_implies_inner_path)
          from `n -ax#asx\<rightarrow>\<^sub>\<iota>* n'` have "sourcenode ax = n"
            by(auto intro:path_split_Cons simp:intra_path_def)
          from `n -ax#asx\<rightarrow>\<^sub>\<iota>* n'` have "n -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'" by simp
          from this `sourcenode a'' = n` `sourcenode ax = n` True
            `n' \<notin> set (sourcenodes (ax#asx))` `valid_edge a''` `intra_kind(kind a'')`
            `inner_node n'` `\<not> method_exit n'` `\<not> n' postdominates targetnode a''`
          have "n controls n'"
            by(fastforce intro!:which_node_intra_standard_control_dependence_source)
          hence "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
            by(fastforce intro:SDG_cdep_edge)
          with `valid_node n` have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
            by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
          moreover
          from `as = (ax#asx)@zs` `sourcenode ax = n` have "n \<in> set(sourcenodes as)"
            by(simp add:sourcenodes_def)
          ultimately show ?thesis by fastforce
        next
          case False
          hence "\<exists>a' \<in> set asx. \<exists>a''. sourcenode a' = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a''"
            by fastforce
          then obtain ax' asx' asx'' where "asx = asx'@ax'#asx'' \<and>
            (\<exists>a''. sourcenode ax' = sourcenode a'' \<and> valid_edge a'' \<and>
            intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'') \<and>
            (\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a''))"
            by(blast elim!:split_list_last_propE)
          then obtain ai where "asx = asx'@ax'#asx''"
            and "sourcenode ax' = sourcenode ai"
            and "valid_edge ai" and "intra_kind(kind ai)"
            and "\<not> n' postdominates targetnode ai"
            and "\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a'')"
            by blast
          from `asx = asx'@ax'#asx''` `n -ax#asx\<rightarrow>\<^sub>\<iota>* n'`
          have "n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'" by simp
          from `n' \<notin> set (sourcenodes (ax#asx))` `asx = asx'@ax'#asx''`
          have "n' \<notin> set (sourcenodes (ax'#asx''))"
            by(auto simp:sourcenodes_def)
          with `inner_node n'` `\<not> n' postdominates targetnode ai`
            `n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'` `sourcenode ax' = sourcenode ai`
            `\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a'')`
            `valid_edge ai` `intra_kind(kind ai)` `\<not> method_exit n'`
          have "sourcenode ax' controls n'"
            by(fastforce intro!:which_node_intra_standard_control_dependence_source)
          hence "CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
            by(fastforce intro:SDG_cdep_edge)
          from `n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'`
          have "n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'" and "valid_edge ax'"
            by(auto intro:path_split simp:intra_path_def simp del:append_Cons)
          from `asx = asx'@ax'#asx''` `as = (ax#asx)@zs`
          have "length (ax#asx') < length as" by simp
          from `as = (ax#asx)@zs` `asx = asx'@ax'#asx''`
          have "sourcenode ax' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def)
          show ?thesis
          proof(cases "n = sourcenode ax'")
            case True
            with `CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'` `valid_edge ax'`
            have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
              by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
            with `sourcenode ax' \<in> set(sourcenodes as)` True show ?thesis by fastforce
          next
            case False
            from `valid_edge ax'` have "sourcenode ax' \<noteq> (_Exit_)"
              by -(rule ccontr,fastforce elim!:Exit_source)
            from `n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'` have "n = sourcenode ax"
              by(fastforce intro:path_split_Cons simp:intra_path_def)
            show ?thesis
            proof(cases "\<forall>ax. valid_edge ax \<and> sourcenode ax = sourcenode ax' \<longrightarrow>
                ax \<notin> get_return_edges a")
              case True
              from `asx = asx'@ax'#asx''` `n -ax#asx\<rightarrow>\<^sub>\<iota>* n'`
              have "intra_kind (kind ax')" by(simp add:intra_path_def)
              have "\<not> method_exit (sourcenode ax')"
              proof
                assume "method_exit (sourcenode ax')"
                thus False
                proof(rule method_exit_cases)
                  assume "sourcenode ax' = (_Exit_)"
                  with `valid_edge ax'` show False by(rule Exit_source)
                next
                  fix x Q f p assume " sourcenode ax' = sourcenode x"
                    and "valid_edge x" and "kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
                  from `valid_edge x` `kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `sourcenode ax' = sourcenode x`
                    `valid_edge ax'` `intra_kind (kind ax')` show False
                    by(fastforce dest:return_edges_only simp:intra_kind_def)
                qed
              qed
              with IH `length (ax#asx') < length as` `n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'`
                `n \<noteq> sourcenode ax'` `sourcenode ax' \<noteq> (_Exit_)` True
              obtain ns where "CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
                and "ns \<noteq> []" 
                and "\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes (ax#asx'))"
                by blast
              from `CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')`
                `CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'`
              have "CFG_node n cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'"
                by(rule cdSp_Append_cdep)
              moreover
              from `\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes (ax#asx'))`
                `asx = asx'@ax'#asx''` `as = (ax#asx)@zs`
                `sourcenode ax' \<in> set(sourcenodes as)`
              have "\<forall>n''\<in>set (ns@[CFG_node (sourcenode ax')]). 
                parent_node n'' \<in> set (sourcenodes as)"
                by(fastforce simp:sourcenodes_def)
              ultimately show ?thesis by fastforce
            next
              case False
              then obtain ai' where "valid_edge ai'" 
                and "sourcenode ai' = sourcenode ax'" 
                and "ai' \<in> get_return_edges a" by blast
              with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `targetnode a = n`
              have "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode ax')"
                by(fastforce intro!:SDG_proc_entry_exit_cdep[of _ _ _ _ _ _ ai'])
              with `valid_node n`
              have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
                by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
              with `CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'`
              have "CFG_node n cd-[CFG_node n]@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* 
                CFG_node n'"
                by(fastforce intro:cdSp_Append_cdep)
              moreover
              from `sourcenode ax' \<in> set(sourcenodes as)` `n = sourcenode ax`
                `as = (ax#asx)@zs`
              have "\<forall>n''\<in>set ([CFG_node n]@[CFG_node (sourcenode ax')]). 
                parent_node n'' \<in> set (sourcenodes as)"
                by(fastforce simp:sourcenodes_def)
              ultimately show ?thesis by fastforce
            qed
          qed
        qed
      qed
    qed
  next
    case False
    then obtain a' where "valid_edge a'" and "sourcenode a' = n'"
      and "a' \<in> get_return_edges a" by auto
    with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `targetnode a = n`
    have "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'" by(fastforce intro:SDG_proc_entry_exit_cdep)
    with `valid_edge a` `targetnode a = n`[THEN sym] 
    have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
      by(fastforce intro:cdep_SDG_path.intros)
    from `n -as\<rightarrow>\<^sub>\<iota>* n'` `n \<noteq> n'` have "as \<noteq> []"
      by(fastforce elim:path.cases simp:intra_path_def)
    with `n -as\<rightarrow>\<^sub>\<iota>* n'` have "hd (sourcenodes as) = n"
      by(fastforce intro:path_sourcenode simp:intra_path_def)
    with `as \<noteq> []` have "n \<in> set (sourcenodes as)" 
      by(fastforce intro:hd_in_set simp:sourcenodes_def)
    with `CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'`
    show ?thesis by auto
  qed
qed


subsection {* Paths consisting of calls and control dependences *}

inductive call_cdep_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ cc-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where ccSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n cc-[]\<rightarrow>\<^sub>d* n"

  | ccSp_Append_cdep:
  "\<lbrakk>n cc-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n cc-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | ccSp_Append_call:
  "\<lbrakk>n cc-ns\<rightarrow>\<^sub>d* n''; n'' -p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> n cc-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma cc_SDG_path_Append:
  "\<lbrakk>n'' cc-ns'\<rightarrow>\<^sub>d* n'; n cc-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n cc-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:call_cdep_SDG_path.induct,
   auto intro:call_cdep_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma cdep_SDG_path_cc_SDG_path:
  "n cd-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n cc-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:cdep_SDG_path.induct,auto intro:call_cdep_SDG_path.intros)


lemma Entry_cc_SDG_path_to_inner_node:
  assumes "valid_SDG_node n" and "parent_node n \<noteq> (_Exit_)"
  obtains ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
proof(atomize_elim)
  obtain m where "m = parent_node n" by simp
  from `valid_SDG_node n` have "valid_node (parent_node n)" 
    by(rule valid_SDG_CFG_node)
  thus "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
  proof(cases "parent_node n" rule:valid_node_cases)
    case Entry
    with `valid_SDG_node n` have "n = CFG_node (_Entry_)" 
      by(rule valid_SDG_node_parent_Entry)
    with `valid_SDG_node n` show ?thesis by(fastforce intro:ccSp_Nil)
  next
    case Exit
    with `parent_node n \<noteq> (_Exit_)` have False by simp
    thus ?thesis by simp
  next
    case inner
    with `m = parent_node n` obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* m"
      by(fastforce dest:Entry_path inner_is_valid)
    then obtain as where "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m"
      and "\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
      by -(erule valid_Entry_path_ascending_path,fastforce)
    from `inner_node (parent_node n)` `m = parent_node n`
    have "inner_node m" by simp
    with `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m` `m = parent_node n` `valid_SDG_node n`
      `\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
    show ?thesis
    proof(induct as arbitrary:m n rule:length_induct)
      fix as m n
      assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
        (\<forall>m'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* m' \<longrightarrow>
        (\<forall>n'. m' = parent_node n' \<longrightarrow> valid_SDG_node n' \<longrightarrow>
        (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)) \<longrightarrow>
        inner_node m' \<longrightarrow> (\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n')))"
        and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m" 
        and "m = parent_node n" and "valid_SDG_node n" and "inner_node m"
        and "\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
      show "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
      proof(cases "\<forall>a' \<in> set as. intra_kind(kind a')")
        case True
        with `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m` have "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m"
          by(fastforce simp:intra_path_def vp_def)
        have "\<not> method_exit m"
        proof
          assume "method_exit m"
          thus False
          proof(rule method_exit_cases)
            assume "m = (_Exit_)"
            with `inner_node m` show False by(simp add:inner_node_def)
          next
            fix a Q f p assume "m = sourcenode a" and "valid_edge a"
              and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m` have "get_proc m = Main"
              by(fastforce dest:intra_path_get_procs simp:get_proc_Entry)
            from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
            have "get_proc (sourcenode a) = p" by(rule get_proc_return)
            with `get_proc m = Main` `m = sourcenode a` have "p = Main" by simp
            with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` show False
              by(fastforce intro:Main_no_return_source)
          qed
        qed
        with `inner_node m` `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m`
        obtain ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
          and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
          by -(erule Entry_cdep_SDG_path)
        then obtain n' where "n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m"
          and "parent_node n' \<in> set(sourcenodes as)"
          by -(erule cdep_SDG_path.cases,auto)
        from `parent_node n' \<in> set(sourcenodes as)` obtain ms ms' 
          where "sourcenodes as = ms@(parent_node n')#ms'"
          by(fastforce dest:split_list simp:sourcenodes_def)
        then obtain as' a as'' where "ms = sourcenodes as'" 
          and "ms' = sourcenodes as''" and "as = as'@a#as''" 
          and "parent_node n' = sourcenode a"
          by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
        with `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m` have "(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:path_split simp:intra_path_def)
        from `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` have "valid_SDG_node n'"
          by(rule SDG_edge_valid_SDG_node)
        hence n'_cases:
          "n' = CFG_node (parent_node n') \<or> CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
          by(rule valid_SDG_node_cases)
        show ?thesis
        proof(cases "as' = []")
          case True
          with `(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'` have "parent_node n' = (_Entry_)"
            by(fastforce simp:intra_path_def)
          from n'_cases have "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
          proof
            assume "n' = CFG_node (parent_node n')"
            with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` `parent_node n' = (_Entry_)`
            have "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* CFG_node m"
              by -(rule cdSp_Append_cdep,rule cdSp_Nil,auto)
            thus ?thesis by fastforce
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with `parent_node n' = (_Entry_)`
            have "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* n'"
              by -(rule cdSp_Append_cdep,rule cdSp_Nil,auto)
            with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m`
            have "CFG_node (_Entry_) cd-[CFG_node (_Entry_)]@[n']\<rightarrow>\<^sub>d* CFG_node m"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
          then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m"
            by(fastforce intro:cdep_SDG_path_cc_SDG_path)
          show ?thesis
          proof(cases "n = CFG_node m")
            case True
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m` 
            show ?thesis by fastforce
          next
            case False
            with `inner_node m` `valid_SDG_node n` `m = parent_node n`
            have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
              by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m`
            have "CFG_node (_Entry_) cc-ns@[CFG_node m]\<rightarrow>\<^sub>d* n"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        next
          case False
          with `as = as'@a#as''` have "length as' < length as" by simp
          from `(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'` have "valid_node (parent_node n')"
            by(fastforce intro:path_valid_node simp:intra_path_def)
          hence "inner_node (parent_node n')"
          proof(cases "parent_node n'" rule:valid_node_cases)
            case Entry
            with `(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* (parent_node n')`
            have "(_Entry_) -as'\<rightarrow>* (_Entry_)" by(fastforce simp:intra_path_def)
            with False have False by fastforce
            thus ?thesis by simp
          next
            case Exit
            with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` have "n' = CFG_node (_Exit_)"
              by -(rule valid_SDG_node_parent_Exit,erule SDG_edge_valid_SDG_node,simp)
            with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` Exit have False
              by simp(erule Exit_no_SDG_edge_source)
            thus ?thesis by simp
          next
            case inner
            thus ?thesis by simp
          qed
          from `valid_node (parent_node n')` 
          have "valid_SDG_node (CFG_node (parent_node n'))" by simp
          from `(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* (parent_node n')` 
          have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (parent_node n')"
            by(rule intra_path_vp)
          from `\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
            `as = as'@a#as''`
          have "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by auto
          with IH `length as' < length as` `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (parent_node n')`
            `valid_SDG_node (CFG_node (parent_node n'))` `inner_node (parent_node n')`
          obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')"
            apply(erule_tac x="as'" in allE) apply clarsimp
            apply(erule_tac x="(parent_node n')" in allE) apply clarsimp
            apply(erule_tac x="CFG_node (parent_node n')" in allE) by clarsimp
          from n'_cases have "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n'"
          proof
            assume "n' = CFG_node (parent_node n')"
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')`
            show ?thesis by fastforce
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')`
            have "CFG_node (_Entry_) cc-ns@[CFG_node (parent_node n')]\<rightarrow>\<^sub>d* n'"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
          then obtain ns' where "CFG_node (_Entry_) cc-ns'\<rightarrow>\<^sub>d* n'" by blast
          with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` 
          have "CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m"
            by(fastforce intro:ccSp_Append_cdep)
          show ?thesis
          proof(cases "n = CFG_node m")
            case True
            with `CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m`
            show ?thesis by fastforce
          next
            case False
            with `inner_node m` `valid_SDG_node n` `m = parent_node n`
            have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
              by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
            with `CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m`
            have "CFG_node (_Entry_) cc-(ns'@[n'])@[CFG_node m]\<rightarrow>\<^sub>d* n"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        qed
      next
        case False
        hence "\<exists>a' \<in> set as. \<not> intra_kind (kind a')" by fastforce
        then obtain a as' as'' where "as = as'@a#as''" and "\<not> intra_kind (kind a)"
          and "\<forall>a' \<in> set as''. intra_kind (kind a')"
          by(fastforce elim!:split_list_last_propE)
        from `\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
          `as = as'@a#as''` `\<not> intra_kind (kind a)`
        obtain Q r p fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by auto
        from `as = as'@a#as''` have "length as' < length as" by fastforce
        from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m` `as = as'@a#as''`
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a" and "valid_edge a"
          and "targetnode a -as''\<rightarrow>\<^sub>\<surd>* m"
          by(auto intro:vp_split)
        hence "valid_SDG_node (CFG_node (sourcenode a))" by simp
        have "\<exists>ns'. CFG_node (_Entry_) cc-ns'\<rightarrow>\<^sub>d* CFG_node m"
        proof(cases "targetnode a = m")
          case True
          with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          have "CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m"
            by(fastforce intro:SDG_call_edge)
          have "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
          proof(cases "as' = []")
            case True
            with `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a` have "(_Entry_) = sourcenode a"
              by(fastforce simp:vp_def)
            with `CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m`
            have "CFG_node (_Entry_) cc-[]\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
              by(fastforce intro:ccSp_Nil SDG_edge_valid_SDG_node)
            thus ?thesis by fastforce
          next
            case False
            from `valid_edge a` have "valid_node (sourcenode a)" by simp
            hence "inner_node (sourcenode a)"
            proof(cases "sourcenode a" rule:valid_node_cases)
              case Entry
              with `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a`
              have "(_Entry_) -as'\<rightarrow>* (_Entry_)" by(fastforce simp:vp_def)
              with False have False by fastforce
              thus ?thesis by simp
            next
              case Exit
              with `valid_edge a` have False by -(erule Exit_source)
              thus ?thesis by simp
            next
              case inner
              thus ?thesis by simp
            qed
            with IH `length as' < length as` `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a`
              `valid_SDG_node (CFG_node (sourcenode a))` 
              `\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
            obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
              apply(erule_tac x="as'" in allE) apply clarsimp
              apply(erule_tac x="sourcenode a" in allE) apply clarsimp
              apply(erule_tac x="CFG_node (sourcenode a)" in allE) by clarsimp
            thus ?thesis by fastforce
          qed
          then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
            by blast
          with `CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m`
          show ?thesis by(fastforce intro:ccSp_Append_call)
        next
          case False
          from `targetnode a -as''\<rightarrow>\<^sub>\<surd>* m` `\<forall>a' \<in> set as''. intra_kind (kind a')`
          have "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m" by(fastforce simp:vp_def intra_path_def)
          hence "get_proc (targetnode a) = get_proc m" by(rule intra_path_get_procs)
          from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (targetnode a) = p"
            by(rule get_proc_call)
          from `inner_node m` `valid_edge a` `targetnode a -as''\<rightarrow>\<^sub>\<iota>* m`
            `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `targetnode a \<noteq> m`
          obtain ns where "CFG_node (targetnode a) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
            and "ns \<noteq> []" 
            and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as'')"
            by(fastforce elim!:in_proc_cdep_SDG_path)
          then obtain n' where "n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m"
            and "parent_node n' \<in> set(sourcenodes as'')"
            by -(erule cdep_SDG_path.cases,auto)
          from `(parent_node n') \<in> set(sourcenodes as'')` obtain ms ms' 
            where "sourcenodes as'' = ms@(parent_node n')#ms'"
            by(fastforce dest:split_list simp:sourcenodes_def)
          then obtain xs a' ys where "ms = sourcenodes xs" 
            and "ms' = sourcenodes ys" and "as'' = xs@a'#ys"
            and "parent_node n' = sourcenode a'"
            by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
          from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m` `as = as'@a#as''` `as'' = xs@a'#ys`
          have "(_Entry_) -(as'@a#xs)@a'#ys\<rightarrow>\<^sub>\<surd>* m" by simp
          hence "(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'"
            and "valid_edge a'" by(auto intro:vp_split)
          from `as = as'@a#as''` `as'' = xs@a'#ys` 
          have "length (as'@a#xs) < length as" by simp
          from `valid_edge a'` have "valid_node (sourcenode a')" by simp
          hence "inner_node (sourcenode a')"
          proof(cases "sourcenode a'" rule:valid_node_cases)
            case Entry
            with `(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'`
            have "(_Entry_) -as'@a#xs\<rightarrow>* (_Entry_)" by(fastforce simp:vp_def)
            hence False by fastforce
            thus ?thesis by simp
          next
            case Exit
            with `valid_edge a'` have False by -(erule Exit_source)
            thus ?thesis by simp
          next
            case inner
            thus ?thesis by simp
          qed
          from `valid_edge a'` have "valid_SDG_node (CFG_node (sourcenode a'))"
            by simp
          from `\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
            `as = as'@a#as''` `as'' = xs@a'#ys`
          have "\<forall>a' \<in> set (as'@a#xs). 
            intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by auto
          with IH `length (as'@a#xs) < length as` 
            `(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'`
            `valid_SDG_node (CFG_node (sourcenode a'))`
            `inner_node (sourcenode a')` `parent_node n' = sourcenode a'`
          obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')"
            apply(erule_tac x="as'@a#xs" in allE) apply clarsimp
            apply(erule_tac x="sourcenode a'" in allE) apply clarsimp
            apply(erule_tac x="CFG_node (sourcenode a')" in allE) by clarsimp
          from `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` have "valid_SDG_node n'"
            by(rule SDG_edge_valid_SDG_node)
          hence "n' = CFG_node (parent_node n') \<or> CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "n' = CFG_node (parent_node n')"
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')`
              `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` show ?thesis
              by(fastforce intro:ccSp_Append_cdep)
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')`
            have "CFG_node (_Entry_) cc-ns@[CFG_node (parent_node n')]\<rightarrow>\<^sub>d* n'"
              by(fastforce intro:ccSp_Append_cdep)
            with `n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m` show ?thesis
              by(fastforce intro:ccSp_Append_cdep)
          qed
        qed
        then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m" by blast
        show ?thesis
        proof(cases "n = CFG_node m")
          case True
          with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m` show ?thesis by fastforce
        next
          case False
          with `inner_node m` `valid_SDG_node n` `m = parent_node n`
          have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
            by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
          with `CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m` show ?thesis
            by(fastforce dest:ccSp_Append_cdep)
        qed
      qed
    qed
  qed
qed


subsection {* Same level paths in the SDG *}

inductive matched :: "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
  where matched_Nil:
  "valid_SDG_node n \<Longrightarrow> matched n [] n"
  | matched_Append_intra_SDG_path:
  "\<lbrakk>matched n ns n''; n'' i-ns'\<rightarrow>\<^sub>d* n'\<rbrakk> \<Longrightarrow> matched n (ns@ns') n'"
  | matched_bracket_call:
  "\<lbrakk>matched n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3; 
    (n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4); valid_edge a; a' \<in> get_return_edges a;
    sourcenode a = parent_node n\<^sub>1; targetnode a = parent_node n\<^sub>2; 
    sourcenode a' = parent_node n\<^sub>3; targetnode a' = parent_node n\<^sub>4\<rbrakk>
  \<Longrightarrow> matched n\<^sub>0 (ns@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
  | matched_bracket_param:
  "\<lbrakk>matched n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3; 
    n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4; valid_edge a; a' \<in> get_return_edges a;
    sourcenode a = parent_node n\<^sub>1; targetnode a = parent_node n\<^sub>2; 
    sourcenode a' = parent_node n\<^sub>3; targetnode a' = parent_node n\<^sub>4\<rbrakk>
  \<Longrightarrow> matched n\<^sub>0 (ns@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"




lemma matched_Append:
  "\<lbrakk>matched n'' ns' n'; matched n ns n''\<rbrakk> \<Longrightarrow> matched n (ns@ns') n'"
by(induct rule:matched.induct,
   auto intro:matched.intros simp:append_assoc[THEN sym] simp del:append_assoc)


lemma intra_SDG_path_matched:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'" shows "matched n ns n'"
proof -
  from `n i-ns\<rightarrow>\<^sub>d* n'` have "valid_SDG_node n"
    by(rule intra_SDG_path_valid_SDG_node)
  hence "matched n [] n" by(rule matched_Nil)
  with `n i-ns\<rightarrow>\<^sub>d* n'` have "matched n ([]@ns) n'"
    by -(rule matched_Append_intra_SDG_path)
  thus ?thesis by simp
qed


lemma intra_proc_matched:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
  shows "matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
                 (CFG_node (sourcenode a'))"
proof -
  from assms have "CFG_node (targetnode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')" 
    by(fastforce intro:SDG_proc_entry_exit_cdep)
  with `valid_edge a` 
  have "CFG_node (targetnode a) i-[]@[CFG_node (targetnode a)]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a')" 
    by(fastforce intro:intra_SDG_path.intros)
  with `valid_edge a` 
  have "matched (CFG_node (targetnode a)) ([]@[CFG_node (targetnode a)])
    (CFG_node (sourcenode a'))"
    by(fastforce intro:matched.intros)
  thus ?thesis by simp
qed


lemma matched_intra_CFG_path:
  assumes "matched n ns n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
proof(atomize_elim)
  from `matched n ns n'` show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case
      by(fastforce dest:empty_path valid_SDG_CFG_node simp:intra_path_def)
  next
    case (matched_Append_intra_SDG_path n ns n'' ns' n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` obtain as 
      where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from `n'' i-ns'\<rightarrow>\<^sub>d* n'` obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce elim:intra_SDG_path_intra_CFG_path)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(rule intra_path_Append)
    thus ?case by fastforce
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from `valid_edge a` `a' \<in> get_return_edges a` `sourcenode a = parent_node n\<^sub>1`
      `targetnode a' = parent_node n\<^sub>4`
    obtain a'' where "valid_edge a''" and "sourcenode a'' = parent_node n\<^sub>1" 
      and "targetnode a'' = parent_node n\<^sub>4" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
      by(fastforce dest:call_return_node_edge)
    hence "parent_node n\<^sub>1 -[a'']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    moreover
    from `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>` have "\<forall>a \<in> set [a'']. intra_kind(kind a)"
      by(fastforce simp:intra_kind_def)
    ultimately have "parent_node n\<^sub>1 -[a'']\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>4"
      by(auto simp:intra_path_def)
    with `\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>1` show ?case
      by(fastforce intro:intra_path_Append)
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from `valid_edge a` `a' \<in> get_return_edges a` `sourcenode a = parent_node n\<^sub>1`
      `targetnode a' = parent_node n\<^sub>4`
    obtain a'' where "valid_edge a''" and "sourcenode a'' = parent_node n\<^sub>1" 
      and "targetnode a'' = parent_node n\<^sub>4" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
      by(fastforce dest:call_return_node_edge)
    hence "parent_node n\<^sub>1 -[a'']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    moreover
    from `kind a'' = (\<lambda>cf. False)\<^sub>\<surd>` have "\<forall>a \<in> set [a'']. intra_kind(kind a)"
      by(fastforce simp:intra_kind_def)
    ultimately have "parent_node n\<^sub>1 -[a'']\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>4"
      by(auto simp:intra_path_def)
    with `\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>1` show ?case
      by(fastforce intro:intra_path_Append)
  qed
qed


lemma matched_same_level_CFG_path:
  assumes "matched n ns n'"
  obtains as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
proof(atomize_elim)
  from `matched n ns n'`
  show "\<exists>as. parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case 
      by(fastforce dest:empty_path valid_SDG_CFG_node simp:slp_def same_level_path_def)
  next
    case (matched_Append_intra_SDG_path n ns n'' ns' n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''" by blast
    from `n'' i-ns'\<rightarrow>\<^sub>d* n'` obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(erule intra_SDG_path_intra_CFG_path)
    from `parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'`
    have "parent_node n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'" by(rule intra_path_slp)
    with `parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''`
    have "parent_node n -as@as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
      by(rule slp_Append)
    thus ?case by fastforce
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from `valid_edge a` `a' \<in> get_return_edges a`
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    from `\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1`
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1" by blast
    from `\<exists>as. parent_node n\<^sub>2 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3`
    obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3" by blast
    from `valid_edge a` `a' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" by(fastforce dest!:call_return_edges)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3` have "same_level_path as'"
      by(simp add:slp_def)
    hence "same_level_path_aux ([]@[a]) as'"
      by(fastforce intro:same_level_path_aux_callstack_Append simp:same_level_path_def)
    from `same_level_path as'` have "upd_cs ([]@[a]) as' = ([]@[a])"
      by(fastforce intro:same_level_path_upd_cs_callstack_Append 
                   simp:same_level_path_def)
    with `same_level_path_aux ([]@[a]) as'` `a' \<in> get_return_edges a`
      `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'`
    have "same_level_path (a#as'@[a'])"
      by(fastforce intro:same_level_path_aux_Append upd_cs_Append 
                   simp:same_level_path_def)
    from `valid_edge a'` `sourcenode a' = parent_node n\<^sub>3`
      `targetnode a' = parent_node n\<^sub>4`
    have "parent_node n\<^sub>3 -[a']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    with `parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3` 
    have "parent_node n\<^sub>2 -as'@[a']\<rightarrow>* parent_node n\<^sub>4"
      by(fastforce intro:path_Append simp:slp_def)
    with `valid_edge a` `sourcenode a = parent_node n\<^sub>1`
      `targetnode a = parent_node n\<^sub>2`
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>* parent_node n\<^sub>4" by -(rule Cons_path)
    with `same_level_path (a#as'@[a'])`
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(simp add:slp_def)
    with `parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1`
    have "parent_node n\<^sub>0 -as@a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(rule slp_Append)
    with `sourcenode a = parent_node n\<^sub>1` `sourcenode a' = parent_node n\<^sub>3`
    show ?case by fastforce
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from `valid_edge a` `a' \<in> get_return_edges a`
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    from `\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1`
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1" by blast
    from `\<exists>as. parent_node n\<^sub>2 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3`
    obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3" by blast
    from `valid_edge a` `a' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" by(fastforce dest!:call_return_edges)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from `parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3` have "same_level_path as'"
      by(simp add:slp_def)
    hence "same_level_path_aux ([]@[a]) as'"
      by(fastforce intro:same_level_path_aux_callstack_Append simp:same_level_path_def)
    from `same_level_path as'` have "upd_cs ([]@[a]) as' = ([]@[a])"
      by(fastforce intro:same_level_path_upd_cs_callstack_Append 
                   simp:same_level_path_def)
    with `same_level_path_aux ([]@[a]) as'` `a' \<in> get_return_edges a`
      `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'`
    have "same_level_path (a#as'@[a'])"
      by(fastforce intro:same_level_path_aux_Append upd_cs_Append 
                   simp:same_level_path_def)
    from `valid_edge a'` `sourcenode a' = parent_node n\<^sub>3`
      `targetnode a' = parent_node n\<^sub>4`
    have "parent_node n\<^sub>3 -[a']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    with `parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3` 
    have "parent_node n\<^sub>2 -as'@[a']\<rightarrow>* parent_node n\<^sub>4"
      by(fastforce intro:path_Append simp:slp_def)
    with `valid_edge a` `sourcenode a = parent_node n\<^sub>1`
      `targetnode a = parent_node n\<^sub>2`
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>* parent_node n\<^sub>4" by -(rule Cons_path)
    with `same_level_path (a#as'@[a'])`
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(simp add:slp_def)
    with `parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1`
    have "parent_node n\<^sub>0 -as@a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(rule slp_Append)
    with `sourcenode a = parent_node n\<^sub>1` `sourcenode a' = parent_node n\<^sub>3`
    show ?case by fastforce
  qed
qed


subsection {*Realizable paths in the SDG *}

inductive realizable :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
  where realizable_matched:"matched n ns n' \<Longrightarrow> realizable n ns n'"
  | realizable_call:
  "\<lbrakk>realizable n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3\<rbrakk>
  \<Longrightarrow> realizable n\<^sub>0 (ns@n\<^sub>1#ns') n\<^sub>3"


lemma realizable_Append_matched:
  "\<lbrakk>realizable n ns n''; matched n'' ns' n'\<rbrakk> \<Longrightarrow> realizable n (ns@ns') n'"
proof(induct rule:realizable.induct)
  case (realizable_matched n ns n'')
  from `matched n'' ns' n'` `matched n ns n''` have "matched n (ns@ns') n'"
    by(rule matched_Append)
  thus ?case by(rule realizable.realizable_matched)
next
  case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns'' n\<^sub>3)
  from `matched n\<^sub>3 ns' n'` `matched n\<^sub>2 ns'' n\<^sub>3` have "matched n\<^sub>2 (ns''@ns') n'"
    by(rule matched_Append)
  with `realizable n\<^sub>0 ns n\<^sub>1` `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2`
  have "realizable n\<^sub>0 (ns@n\<^sub>1#(ns''@ns')) n'"
    by(rule realizable.realizable_call)
  thus ?case by simp
qed


lemma realizable_valid_CFG_path:
  assumes "realizable n ns n'" 
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<surd>* parent_node n'"
proof(atomize_elim)
  from `realizable n ns n'` 
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<surd>* parent_node n'"
  proof(induct rule:realizable.induct)
    case (realizable_matched n ns n')
    from `matched n ns n'` obtain as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
      by(erule matched_same_level_CFG_path)
    thus ?case by(fastforce intro:slp_vp)
  next
    case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns' n\<^sub>3)
    from `\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1`
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1" by blast
    from `matched n\<^sub>2 ns' n\<^sub>3` obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3"
      by(erule matched_same_level_CFG_path)
    from `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2`
    obtain a Q r fs where "valid_edge a"
      and "sourcenode a = parent_node n\<^sub>1" and "targetnode a = parent_node n\<^sub>2"
      and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by(fastforce elim:SDG_edge.cases)+
    hence "parent_node n\<^sub>1 -[a]\<rightarrow>* parent_node n\<^sub>2"
      by(fastforce dest:path_edge)
    from `parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1` 
    have "parent_node n\<^sub>0 -as\<rightarrow>* parent_node n\<^sub>1" and "valid_path as"
      by(simp_all add:vp_def)
    with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "valid_path (as@[a])"
      by(fastforce elim:valid_path_aux_Append simp:valid_path_def)
    moreover
    from `parent_node n\<^sub>0 -as\<rightarrow>* parent_node n\<^sub>1` `parent_node n\<^sub>1 -[a]\<rightarrow>* parent_node n\<^sub>2`
    have "parent_node n\<^sub>0 -as@[a]\<rightarrow>* parent_node n\<^sub>2" by(rule path_Append)
    ultimately have "parent_node n\<^sub>0 -as@[a]\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>2" by(simp add:vp_def)
    with `parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3` 
    have "parent_node n\<^sub>0 -(as@[a])@as'\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>3" by -(rule vp_slp_Append)
    with `sourcenode a = parent_node n\<^sub>1` show ?case by fastforce
  qed
qed


lemma cdep_SDG_path_realizable:
  "n cc-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> realizable n ns n'"
proof(induct rule:call_cdep_SDG_path.induct)
  case (ccSp_Nil n)
  from `valid_SDG_node n` show ?case
    by(fastforce intro:realizable_matched matched_Nil)
next
  case (ccSp_Append_cdep n ns n'' n')
  from `n'' \<longrightarrow>\<^bsub>cd\<^esub> n'` have "valid_SDG_node n''" by(rule SDG_edge_valid_SDG_node)
  hence "matched n'' [] n''" by(rule matched_Nil)
  from `n'' \<longrightarrow>\<^bsub>cd\<^esub> n'` `valid_SDG_node n''`
  have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'" 
    by(fastforce intro:iSp_Append_cdep iSp_Nil)
  with `matched n'' [] n''` have "matched n'' ([]@[n'']) n'"
    by(fastforce intro:matched_Append_intra_SDG_path)
  with `realizable n ns n''` show ?case
    by(fastforce intro:realizable_Append_matched)
next
  case (ccSp_Append_call n ns n'' p n')
  from `n'' -p\<rightarrow>\<^bsub>call\<^esub> n'` have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
  hence "matched n' [] n'" by(rule matched_Nil)
  with `realizable n ns n''` `n'' -p\<rightarrow>\<^bsub>call\<^esub> n'`
  show ?case by(fastforce intro:realizable_call)
qed


subsection {* SDG with summary edges *}


inductive sum_cdep_edge :: "'node SDG_node \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s\<longrightarrow>\<^bsub>cd\<^esub> _" [51,0] 80)
  and sum_ddep_edge :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_\<rightarrow>\<^bsub>dd\<^esub> _" [51,0,0] 80)
  and sum_call_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>call\<^esub> _" [51,0,0] 80)
  and sum_return_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>ret\<^esub> _" [51,0,0] 80)
  and sum_param_in_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_:_\<rightarrow>\<^bsub>in\<^esub> _" [51,0,0,0] 80)
  and sum_param_out_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_:_\<rightarrow>\<^bsub>out\<^esub> _" [51,0,0,0] 80)
  and sum_summary_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>sum\<^esub> _" [51,0] 80)
  and sum_SDG_edge :: "'node SDG_node \<Rightarrow> 'var option \<Rightarrow> 
                          ('pname \<times> bool) option \<Rightarrow> bool \<Rightarrow> 'node SDG_node \<Rightarrow> bool"

where
    (* Syntax *)
  "n s\<longrightarrow>\<^bsub>cd\<^esub> n' == sum_SDG_edge n None None False n'"
  | "n s-V\<rightarrow>\<^bsub>dd\<^esub> n' == sum_SDG_edge n (Some V) None False n'"
  | "n s-p\<rightarrow>\<^bsub>call\<^esub> n' == sum_SDG_edge n None (Some(p,True)) False n'"
  | "n s-p\<rightarrow>\<^bsub>ret\<^esub> n' == sum_SDG_edge n None (Some(p,False)) False n'"
  | "n s-p:V\<rightarrow>\<^bsub>in\<^esub> n' == sum_SDG_edge n (Some V) (Some(p,True)) False n'"
  | "n s-p:V\<rightarrow>\<^bsub>out\<^esub> n' == sum_SDG_edge n (Some V) (Some(p,False)) False n'"
  | "n s-p\<rightarrow>\<^bsub>sum\<^esub> n' == sum_SDG_edge n None (Some(p,True)) True n'"

    (* Rules *)
  | sum_SDG_cdep_edge:
    "\<lbrakk>n = CFG_node m; n' = CFG_node m'; m controls m'\<rbrakk> \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_proc_entry_exit_cdep:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (targetnode a);
      a' \<in> get_return_edges a; n' = CFG_node (sourcenode a')\<rbrakk> \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_parent_cdep_edge:
    "\<lbrakk>valid_SDG_node n'; m = parent_node n'; n = CFG_node m; n \<noteq> n'\<rbrakk> 
      \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_ddep_edge:"n influences V in n' \<Longrightarrow> n s-V\<rightarrow>\<^bsub>dd\<^esub> n'"
  | sum_SDG_call_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n s-p\<rightarrow>\<^bsub>call\<^esub> n'"
  | sum_SDG_return_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n s-p\<rightarrow>\<^bsub>ret\<^esub> n'"
  | sum_SDG_param_in_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs; V = ins!x;
      x < length ins; n = Actual_in (sourcenode a,x); n' = Formal_in (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n s-p:V\<rightarrow>\<^bsub>in\<^esub> n'"
  | sum_SDG_param_out_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs; V = outs!x;
      x < length outs; n = Formal_out (sourcenode a,x); 
      n' = Actual_out (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
  | sum_SDG_call_summary_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a; 
      n = CFG_node (sourcenode a); n' = CFG_node (targetnode a')\<rbrakk>
      \<Longrightarrow> n s-p\<rightarrow>\<^bsub>sum\<^esub> n'"
  | sum_SDG_param_summary_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
      matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'));
      n = Actual_in (sourcenode a,x); n' = Actual_out (targetnode a',x');
      (p,ins,outs) \<in> set procs; x < length ins; x' < length outs\<rbrakk>
      \<Longrightarrow> n s-p\<rightarrow>\<^bsub>sum\<^esub> n'"



lemma sum_edge_cases:
  "\<lbrakk>n s-p\<rightarrow>\<^bsub>sum\<^esub> n'; 
    \<And>a Q r fs a'. \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
                n = CFG_node (sourcenode a); n' = CFG_node (targetnode a')\<rbrakk> \<Longrightarrow> P;
    \<And>a Q p r fs a' ns x x' ins outs.
      \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
       matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'));
       n = Actual_in (sourcenode a,x); n' = Actual_out (targetnode a',x');
       (p,ins,outs) \<in> set procs; x < length ins; x' < length outs\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
by -(erule sum_SDG_edge.cases,auto)



lemma SDG_edge_sum_SDG_edge:
  "SDG_edge n Vopt popt n' \<Longrightarrow> sum_SDG_edge n Vopt popt False n'"
  by(induct rule:SDG_edge.induct,auto intro:sum_SDG_edge.intros)


lemma sum_SDG_edge_SDG_edge:
  "sum_SDG_edge n Vopt popt False n' \<Longrightarrow> SDG_edge n Vopt popt n'"
by(induct n Vopt popt x\<equiv>"False" n' rule:sum_SDG_edge.induct,
   auto intro:SDG_edge.intros)


lemma sum_SDG_edge_valid_SDG_node:
  assumes "sum_SDG_edge n Vopt popt b n'" 
  shows "valid_SDG_node n" and "valid_SDG_node n'"
proof -
  have "valid_SDG_node n \<and> valid_SDG_node n'"
  proof(cases b)
    case True
    with `sum_SDG_edge n Vopt popt b n'` show ?thesis
    proof(induct rule:sum_SDG_edge.induct)
      case (sum_SDG_call_summary_edge a Q r p f a' n n')
      from `valid_edge a` `n = CFG_node (sourcenode a)`
      have "valid_SDG_node n" by fastforce
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
        by(rule get_return_edges_valid)
      with `n' = CFG_node (targetnode a')` have "valid_SDG_node n'" by fastforce
      with `valid_SDG_node n` show ?case by simp
    next
      case (sum_SDG_param_summary_edge a Q r p fs a' x ns x' n n' ins outs)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `n = Actual_in (sourcenode a,x)`
        `(p,ins,outs) \<in> set procs` `x < length ins`
      have "valid_SDG_node n" by fastforce
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
        by(rule get_return_edges_valid)
      from `valid_edge a` `a' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      with `valid_edge a'` `n' = Actual_out (targetnode a',x')`
        `(p,ins,outs) \<in> set procs` `x' < length outs`
      have "valid_SDG_node n'" by fastforce
      with `valid_SDG_node n` show ?case by simp
    qed simp_all
  next
    case False
    with `sum_SDG_edge n Vopt popt b n'` have "SDG_edge n Vopt popt n'"
      by(fastforce intro:sum_SDG_edge_SDG_edge)
    thus ?thesis by(fastforce intro:SDG_edge_valid_SDG_node)
  qed
  thus "valid_SDG_node n" and "valid_SDG_node n'" by simp_all
qed


lemma Exit_no_sum_SDG_edge_source:
  assumes "sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'" shows "False"
proof(cases b)
  case True
  with `sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'` show ?thesis
  proof(induct "CFG_node (_Exit_)" Vopt popt b n' rule:sum_SDG_edge.induct)
    case (sum_SDG_call_summary_edge a Q r p f a' n')
    from `CFG_node (_Exit_) = CFG_node (sourcenode a)`
    have "sourcenode a = (_Exit_)" by simp
    with `valid_edge a` show ?case by(rule Exit_source)
  next
    case (sum_SDG_param_summary_edge a Q r p f a' x ns x' n' ins outs)
    thus ?case by simp
  qed simp_all
next
  case False
  with `sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'` 
  have "SDG_edge (CFG_node (_Exit_)) Vopt popt n'"
    by(fastforce intro:sum_SDG_edge_SDG_edge)
  thus ?thesis by(fastforce intro:Exit_no_SDG_edge_source)
qed


lemma Exit_no_sum_SDG_edge_target:
  "sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)) \<Longrightarrow> False"
proof(induct "CFG_node (_Exit_)" rule:sum_SDG_edge.induct)
  case (sum_SDG_cdep_edge n m m')
  from `m controls m'` `CFG_node (_Exit_) = CFG_node m'`
  have "m controls (_Exit_)" by simp
  hence False by(fastforce dest:Exit_not_control_dependent)
  thus ?case by simp
next
  case (sum_SDG_proc_entry_exit_cdep a Q r p f n a')
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
    by(rule get_return_edges_valid)
  moreover
  from `CFG_node (_Exit_) = CFG_node (sourcenode a')`
  have "sourcenode a' = (_Exit_)" by simp
  ultimately have False by(rule Exit_source)
  thus ?case by simp
next
  case (sum_SDG_ddep_edge n V) thus ?case
    by(fastforce elim:SDG_Use.cases simp:data_dependence_def)
next
  case (sum_SDG_call_edge a Q r p fs n)
  from `CFG_node (_Exit_) = CFG_node (targetnode a)`
  have "targetnode a = (_Exit_)" by simp
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have "get_proc (_Exit_) = p"
    by(fastforce intro:get_proc_call)
  hence "p = Main" by(simp add:get_proc_Exit)
  with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` have False 
    by(fastforce intro:Main_no_call_target)
  thus ?case by simp
next
  case (sum_SDG_return_edge a Q p f n)
  from `CFG_node (_Exit_) = CFG_node (targetnode a)`
  have "targetnode a = (_Exit_)" by simp
  with `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have False by(rule Exit_no_return_target)
  thus ?case by simp
next
  case (sum_SDG_call_summary_edge a Q r p fs a' n)
  from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
    by(rule get_return_edges_valid)
  from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
  obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
  from `CFG_node (_Exit_) = CFG_node (targetnode a')`
  have "targetnode a' = (_Exit_)" by simp
  with `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` have False by(rule Exit_no_return_target)
  thus ?case by simp
qed simp+



lemma sum_SDG_summary_edge_matched:
  assumes "n s-p\<rightarrow>\<^bsub>sum\<^esub> n'" 
  obtains ns where "matched n ns n'" and "n \<in> set ns"
  and "get_proc (parent_node(last ns)) = p"
proof(atomize_elim)
  from `n s-p\<rightarrow>\<^bsub>sum\<^esub> n'` 
  show "\<exists>ns. matched n ns n' \<and> n \<in> set ns \<and> get_proc (parent_node(last ns)) = p"
  proof(induct n "None::'var option" "Some(p,True)" "True" n'
               rule:sum_SDG_edge.induct)
    case (sum_SDG_call_summary_edge a Q r fs a' n n')
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `n = CFG_node (sourcenode a)`
    have "n -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)" by(fastforce intro:SDG_call_edge)
    hence "valid_SDG_node n" by(rule SDG_edge_valid_SDG_node)
    hence "matched n [] n" by(rule matched_Nil)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
      by(rule get_return_edges_valid)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a` 
    have matched:"matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
      (CFG_node (sourcenode a'))" by(rule intra_proc_matched)
    from `valid_edge a` `a' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
    with `valid_edge a'` have "get_proc (sourcenode a') = p" by(rule get_proc_return)
    from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `n' = CFG_node (targetnode a')`
    have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'" by(fastforce intro:SDG_return_edge)
    from `matched n [] n` `n -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)` matched
      `CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'` `a' \<in> get_return_edges a`
      `n = CFG_node (sourcenode a)` `n' = CFG_node (targetnode a')` `valid_edge a`
    have "matched n ([]@n#[CFG_node (targetnode a)]@[CFG_node (sourcenode a')]) n'"
      by(fastforce intro:matched_bracket_call)
    with `get_proc (sourcenode a') = p` show ?case by auto
  next
    case (sum_SDG_param_summary_edge a Q r fs a' x ns x' n n' ins outs)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
      `x < length ins` `n = Actual_in (sourcenode a,x)`
    have "n -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)" 
      by(fastforce intro:SDG_param_in_edge)
    hence "valid_SDG_node n" by(rule SDG_edge_valid_SDG_node)
    hence "matched n [] n" by(rule matched_Nil)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
      by(rule get_return_edges_valid)
    from `valid_edge a` `a' \<in> get_return_edges a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
    with `valid_edge a'` have "get_proc (sourcenode a') = p" by(rule get_proc_return)
    from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `(p,ins,outs) \<in> set procs`
      `x' < length outs` `n' = Actual_out (targetnode a',x')`
    have "Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'"
      by(fastforce intro:SDG_param_out_edge)
    from `matched n [] n` `n -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)`
      `matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'))`
      `Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'` 
      `a' \<in> get_return_edges a` `n = Actual_in (sourcenode a,x)`
      `n' = Actual_out (targetnode a',x')` `valid_edge a`
    have "matched n ([]@n#ns@[Formal_out (sourcenode a',x')]) n'"
      by(fastforce intro:matched_bracket_param)
    with `get_proc (sourcenode a') = p` show ?case by auto
  qed simp_all
qed


lemma return_edge_determines_call_and_sum_edge:
  assumes "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  obtains a' Q' r' fs' where "a \<in> get_return_edges a'" and "valid_edge a'"
  and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" 
  and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
proof(atomize_elim)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
  have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
    by(fastforce intro:sum_SDG_return_edge)
  from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
  obtain a' Q' r' fs' where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
    and "a \<in> get_return_edges a'" by(blast dest:return_needs_call)
  hence "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
    by(fastforce intro:sum_SDG_call_edge)
  from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `valid_edge a` `a \<in> get_return_edges a'`
  have "CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)"
    by(fastforce intro!:SDG_proc_entry_exit_cdep)
  hence "valid_SDG_node (CFG_node (targetnode a'))"
    by(rule SDG_edge_valid_SDG_node)
  with `CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)` 
  have "CFG_node (targetnode a') i-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a)"
    by(fastforce intro:iSp_Append_cdep iSp_Nil)
  from `valid_SDG_node (CFG_node (targetnode a'))` 
  have "matched (CFG_node (targetnode a')) [] (CFG_node (targetnode a'))"
    by(rule matched_Nil)
  with `CFG_node (targetnode a') i-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a)`
  have "matched (CFG_node (targetnode a')) ([]@[CFG_node (targetnode a')])
                (CFG_node (sourcenode a))"
    by(fastforce intro:matched_Append_intra_SDG_path)
  with `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
    `a \<in> get_return_edges a'`
  have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by(fastforce intro!:sum_SDG_call_summary_edge)
  with `a \<in> get_return_edges a'` `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
  show "\<exists>a' Q' r' fs'. a \<in> get_return_edges a' \<and> valid_edge a' \<and> 
    kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs' \<and> CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by fastforce
qed
  

subsection {* Paths consisting of intraprocedural and summary edges in the SDG *}

inductive intra_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ is-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where isSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n is-[]\<rightarrow>\<^sub>d* n"

  | isSp_Append_cdep:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | isSp_Append_ddep:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | isSp_Append_sum:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma is_SDG_path_Append:
  "\<lbrakk>n'' is-ns'\<rightarrow>\<^sub>d* n'; n is-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n is-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_sum_SDG_path.induct,
   auto intro:intra_sum_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma is_SDG_path_valid_SDG_node:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using `n is-ns\<rightarrow>\<^sub>d* n'`
by(induct rule:intra_sum_SDG_path.induct,
   auto intro:sum_SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma intra_SDG_path_is_SDG_path:
  "n i-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n is-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_SDG_path.induct,
   auto intro:intra_sum_SDG_path.intros SDG_edge_sum_SDG_edge)


lemma is_SDG_path_hd:"\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; ns \<noteq> []\<rbrakk> \<Longrightarrow> hd ns = n"
apply(induct rule:intra_sum_SDG_path.induct) apply clarsimp
by(case_tac ns,auto elim:intra_sum_SDG_path.cases)+


lemma intra_sum_SDG_path_rev_induct [consumes 1, case_names "isSp_Nil" 
  "isSp_Cons_cdep"  "isSp_Cons_ddep"  "isSp_Cons_sum"]: 
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  and refl:"\<And>n. valid_SDG_node n \<Longrightarrow> P n [] n"
  and step_cdep:"\<And>n ns n' n''. \<lbrakk>n s\<longrightarrow>\<^bsub>cd\<^esub> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; P n'' ns n'\<rbrakk> 
                 \<Longrightarrow> P n (n#ns) n'"
  and step_ddep:"\<And>n ns n' V n''. \<lbrakk>n s-V\<rightarrow>\<^bsub>dd\<^esub> n''; n \<noteq> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; 
                                  P n'' ns n'\<rbrakk> \<Longrightarrow> P n (n#ns) n'"
  and step_sum:"\<And>n ns n' p n''. \<lbrakk>n s-p\<rightarrow>\<^bsub>sum\<^esub> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; P n'' ns n'\<rbrakk> 
                 \<Longrightarrow> P n (n#ns) n'"
  shows "P n ns n'"
using `n is-ns\<rightarrow>\<^sub>d* n'`
proof(induct ns arbitrary:n)
  case Nil thus ?case by(fastforce elim:intra_sum_SDG_path.cases intro:refl)
next
  case (Cons nx nsx)
  note IH = `\<And>n. n is-nsx\<rightarrow>\<^sub>d* n' \<Longrightarrow> P n nsx n'`
  from `n is-nx#nsx\<rightarrow>\<^sub>d* n'` have [simp]:"n = nx" 
    by(fastforce dest:is_SDG_path_hd)
  from `n is-nx#nsx\<rightarrow>\<^sub>d* n'`  have "((\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n') \<or>
    (\<exists>n'' V. n s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> n \<noteq> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n')) \<or>
    (\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n')"
  proof(induct nsx arbitrary:n' rule:rev_induct)
    case Nil
    from `n is-[nx]\<rightarrow>\<^sub>d* n'` have "n is-[]\<rightarrow>\<^sub>d* nx" 
      and disj:"nx s\<longrightarrow>\<^bsub>cd\<^esub> n' \<or> (\<exists>V. nx s-V\<rightarrow>\<^bsub>dd\<^esub> n' \<and> nx \<noteq> n') \<or> (\<exists>p. nx s-p\<rightarrow>\<^bsub>sum\<^esub> n')"
      by(induct n ns\<equiv>"[nx]" n' rule:intra_sum_SDG_path.induct,auto)
    from `n is-[]\<rightarrow>\<^sub>d* nx` have [simp]:"n = nx"
      by(fastforce elim:intra_sum_SDG_path.cases)
    from disj have "valid_SDG_node n'" by(fastforce intro:sum_SDG_edge_valid_SDG_node)
    hence "n' is-[]\<rightarrow>\<^sub>d* n'" by(rule isSp_Nil)
    with disj show ?case by fastforce
  next
    case (snoc x xs)
    note `\<And>n'. n is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
      ((\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
      (\<exists>n'' V. n s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> n \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
      (\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')`
    with `n is-nx#xs@[x]\<rightarrow>\<^sub>d* n'` show ?case
    proof(induct n "nx#xs@[x]" n' rule:intra_sum_SDG_path.induct)
      case (isSp_Append_cdep m ms m'' n')
      note IH = `\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')`
      from `ms @ [m''] = nx#xs@[x]` have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from `m is-ms\<rightarrow>\<^sub>d* m''` have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from `n'' is-xs\<rightarrow>\<^sub>d* m''` `m'' s\<longrightarrow>\<^bsub>cd\<^esub> n'`
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with `(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')`
      show ?case by fastforce
    next
      case (isSp_Append_ddep m ms m'' V n')
      note IH = `\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')`
      from `ms @ [m''] = nx#xs@[x]` have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from `m is-ms\<rightarrow>\<^sub>d* m''` have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from `n'' is-xs\<rightarrow>\<^sub>d* m''` `m'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `m'' \<noteq> n'`
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with `(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')`
      show ?case by fastforce
    next
      case (isSp_Append_sum m ms m'' p n')
      note IH = `\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')`
      from `ms @ [m''] = nx#xs@[x]` have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from `m is-ms\<rightarrow>\<^sub>d* m''` have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from `n'' is-xs\<rightarrow>\<^sub>d* m''` `m'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'`
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with `(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')`
      show ?case by fastforce
    qed
  qed
  thus ?case apply -
  proof(erule disjE)+
    assume "\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' where "n s\<longrightarrow>\<^bsub>cd\<^esub> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" by blast
    from IH[OF `n'' is-nsx\<rightarrow>\<^sub>d* n'`] have "P n'' nsx n'" .
    from step_cdep[OF `n s\<longrightarrow>\<^bsub>cd\<^esub> n''` `n'' is-nsx\<rightarrow>\<^sub>d* n'` this] show ?thesis by simp
  next
    assume "\<exists>n'' V. n s-V\<rightarrow>\<^bsub>dd\<^esub> n'' \<and> n \<noteq> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' V where "n s-V\<rightarrow>\<^bsub>dd\<^esub> n''" and "n \<noteq> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" 
      by blast
    from IH[OF `n'' is-nsx\<rightarrow>\<^sub>d* n'`] have "P n'' nsx n'" .
    from step_ddep[OF `n s-V\<rightarrow>\<^bsub>dd\<^esub> n''` `n \<noteq> n''` `n'' is-nsx\<rightarrow>\<^sub>d* n'` this] 
    show ?thesis by simp
  next
    assume "\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' p where "n s-p\<rightarrow>\<^bsub>sum\<^esub> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" by blast
    from IH[OF `n'' is-nsx\<rightarrow>\<^sub>d* n'`] have "P n'' nsx n'" .
    from step_sum[OF `n s-p\<rightarrow>\<^bsub>sum\<^esub> n''` `n'' is-nsx\<rightarrow>\<^sub>d* n'` this] show ?thesis by simp
  qed
qed


lemma is_SDG_path_CFG_path:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from `n is-ns\<rightarrow>\<^sub>d* n'`
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from `valid_SDG_node n` have "valid_node (parent_node n)"
      by(rule valid_SDG_CFG_node)
    hence "parent_node n -[]\<rightarrow>* parent_node n" by(rule empty_path)
    thus ?case by(auto simp:intra_path_def)
  next
    case (isSp_Append_cdep n ns n'' n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'`  have "n'' \<longrightarrow>\<^bsub>cd\<^esub> n'" by(rule sum_SDG_edge_SDG_edge)
    thus ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with `parent_node n'' = targetnode a` `parent_node n' = sourcenode a'` 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` show ?thesis by fastforce
    qed
  next
    case (isSp_Append_ddep n ns n'' V n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast 
    from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "n'' influences V in n'"
      by(fastforce elim:sum_SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  next
    case (isSp_Append_sum n ns n'' p n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'` have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
    proof(rule sum_edge_cases)
      fix a Q fs a'
      assume "valid_edge a" and "a' \<in> get_return_edges a"
        and "n'' = CFG_node (sourcenode a)" and "n' = CFG_node (targetnode a')"
      from `valid_edge a` `a' \<in> get_return_edges a`
      obtain a'' where "sourcenode a -[a'']\<rightarrow>\<^sub>\<iota>* targetnode a'"
        apply - apply(drule call_return_node_edge)
        apply(auto simp:intra_path_def) apply(drule path_edge)
        by(auto simp:intra_kind_def)
      with `n'' = CFG_node (sourcenode a)` `n' = CFG_node (targetnode a')`
      show ?thesis by simp blast
    next
      fix a Q p fs a' ns x x' ins outs
      assume "valid_edge a" and "a' \<in> get_return_edges a"
        and "n'' = Actual_in (sourcenode a, x)" 
        and "n' = Actual_out (targetnode a', x')"
      from `valid_edge a` `a' \<in> get_return_edges a`
      obtain a'' where "sourcenode a -[a'']\<rightarrow>\<^sub>\<iota>* targetnode a'"
        apply - apply(drule call_return_node_edge)
        apply(auto simp:intra_path_def) apply(drule path_edge)
        by(auto simp:intra_kind_def)
      with `n'' = Actual_in (sourcenode a, x)` `n' = Actual_out (targetnode a', x')`
      show ?thesis by simp blast
    qed
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by blast
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  qed
qed


lemma matched_is_SDG_path:
  assumes "matched n ns n'" obtains ns' where "n is-ns'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from `matched n ns n'` show "\<exists>ns'. n is-ns'\<rightarrow>\<^sub>d* n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case by(fastforce intro:isSp_Nil)
  next
    case matched_Append_intra_SDG_path thus ?case
    by(fastforce intro:is_SDG_path_Append intra_SDG_path_is_SDG_path)
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from `\<exists>ns'. n\<^sub>0 is-ns'\<rightarrow>\<^sub>d* n\<^sub>1` obtain nsx where "n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    from `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2` `sourcenode a = parent_node n\<^sub>1` `targetnode a = parent_node n\<^sub>2`
    have "n\<^sub>1 = CFG_node (sourcenode a)" and "n\<^sub>2 = CFG_node (targetnode a)"
      by(auto elim:SDG_edge.cases)
    from `valid_edge a` `a' \<in> get_return_edges a`
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    with `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2` `valid_edge a`
      `n\<^sub>1 = CFG_node (sourcenode a)` `n\<^sub>2 = CFG_node (targetnode a)`
    have [simp]:"p' = p" by -(erule SDG_edge.cases,(fastforce dest:edge_det)+)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
      by(rule get_return_edges_valid)
    from `n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4` show ?case
    proof
      assume "n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4"
      then obtain ax Q' f' where "valid_edge ax" and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
        and "n\<^sub>3 = CFG_node (sourcenode ax)" and "n\<^sub>4 = CFG_node (targetnode ax)"
        by(fastforce elim:SDG_edge.cases)
      with `sourcenode a' = parent_node n\<^sub>3` `targetnode a' = parent_node n\<^sub>4` 
        `valid_edge a'` have [simp]:"ax = a'" by(fastforce dest:edge_det)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `valid_edge ax` `kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
        `a' \<in> get_return_edges a` `matched n\<^sub>2 ns' n\<^sub>3`
        `n\<^sub>1 = CFG_node (sourcenode a)` `n\<^sub>2 = CFG_node (targetnode a)`
        `n\<^sub>3 = CFG_node (sourcenode ax)` `n\<^sub>4 = CFG_node (targetnode ax)`
      have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> n\<^sub>4" 
        by(fastforce intro!:sum_SDG_call_summary_edge[of a _ _ _ _ ax])
      with `n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1` have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>4" by(rule isSp_Append_sum)
      thus ?case by blast
    next
      assume "n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4"
      then obtain ax Q' f' x where "valid_edge ax" and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
        and "n\<^sub>3 = Formal_out (sourcenode ax,x)" 
        and "n\<^sub>4 = Actual_out (targetnode ax,x)"
        by(fastforce elim:SDG_edge.cases)
      with `sourcenode a' = parent_node n\<^sub>3` `targetnode a' = parent_node n\<^sub>4` 
        `valid_edge a'` have [simp]:"ax = a'" by(fastforce dest:edge_det)
      from `valid_edge ax` `kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `n\<^sub>3 = Formal_out (sourcenode ax,x)`
        `n\<^sub>4 = Actual_out (targetnode ax,x)`
      have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a')"
        by(fastforce intro:SDG_return_edge)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `valid_edge a'` 
        `a' \<in> get_return_edges a` `n\<^sub>4 = Actual_out (targetnode ax,x)`
      have "CFG_node (targetnode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')"
        by(fastforce intro!:SDG_proc_entry_exit_cdep)
      with `n\<^sub>2 = CFG_node (targetnode a)`
      have "matched n\<^sub>2 ([]@([]@[n\<^sub>2])) (CFG_node (sourcenode a'))"
        by(fastforce intro:matched.intros intra_SDG_path.intros 
                          SDG_edge_valid_SDG_node) 
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `valid_edge a'` `kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
        `a' \<in> get_return_edges a` `n\<^sub>1 = CFG_node (sourcenode a)` 
        `n\<^sub>2 = CFG_node (targetnode a)` `n\<^sub>4 = Actual_out (targetnode ax,x)`
      have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
        by(fastforce intro!:sum_SDG_call_summary_edge[of a _ _ _ _ a'])
      with `n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1` have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* CFG_node (targetnode a')"
        by(rule isSp_Append_sum)
      from `n\<^sub>4 = Actual_out (targetnode ax,x)` `n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4`
      have "CFG_node (targetnode a') s\<longrightarrow>\<^bsub>cd\<^esub> n\<^sub>4"
        by(fastforce intro:sum_SDG_parent_cdep_edge SDG_edge_valid_SDG_node)
      with `n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* CFG_node (targetnode a')`
      have "n\<^sub>0 is-(nsx@[n\<^sub>1])@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* n\<^sub>4"
        by(rule isSp_Append_cdep)
      thus ?case by blast
    qed
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from `\<exists>ns'. n\<^sub>0 is-ns'\<rightarrow>\<^sub>d* n\<^sub>1` obtain nsx where "n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    from `n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2` `sourcenode a = parent_node n\<^sub>1`
      `targetnode a = parent_node n\<^sub>2` obtain x ins outs
      where "n\<^sub>1 = Actual_in (sourcenode a,x)" and "n\<^sub>2 = Formal_in (targetnode a,x)"
      and "(p,ins,outs) \<in> set procs" and "V = ins!x" and "x < length ins"
      by(fastforce elim:SDG_edge.cases)
    from `valid_edge a` `a' \<in> get_return_edges a`
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs"
      by(fastforce dest!:only_call_get_return_edges)
    with `n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2` `valid_edge a`
      `n\<^sub>1 = Actual_in (sourcenode a,x)` `n\<^sub>2 = Formal_in (targetnode a,x)`
    have [simp]:"p' = p" by -(erule SDG_edge.cases,(fastforce dest:edge_det)+)
    from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
      by(rule get_return_edges_valid)
    from `n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4` obtain ax Q' f' x' ins' outs' where "valid_edge ax" 
      and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "n\<^sub>3 = Formal_out (sourcenode ax,x')" 
      and "n\<^sub>4 = Actual_out (targetnode ax,x')" and "(p,ins',outs') \<in> set procs"
      and "V' = outs'!x'" and "x' < length outs'"
      by(fastforce elim:SDG_edge.cases)
    with `sourcenode a' = parent_node n\<^sub>3` `targetnode a' = parent_node n\<^sub>4`
      `valid_edge a'` have [simp]:"ax = a'" by(fastforce dest:edge_det)
    from unique_callers `(p,ins,outs) \<in> set procs` `(p,ins',outs') \<in> set procs`
    have [simp]:"ins = ins'" "outs = outs'"
      by(auto dest:distinct_fst_isin_same_fst)
    from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs` `valid_edge a'` `kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'`
      `a' \<in> get_return_edges a` `matched n\<^sub>2 ns' n\<^sub>3` `n\<^sub>1 = Actual_in (sourcenode a,x)` 
      `n\<^sub>2 = Formal_in (targetnode a,x)` `n\<^sub>3 = Formal_out (sourcenode ax,x')`
      `n\<^sub>4 = Actual_out (targetnode ax,x')` `(p,ins,outs) \<in> set procs`
      `x < length ins` `x' < length outs'` `V = ins!x` `V' = outs'!x'`
    have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> n\<^sub>4" 
      by(fastforce intro!:sum_SDG_param_summary_edge[of a _ _ _ _ a'])
    with `n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1` have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>4" by(rule isSp_Append_sum)
    thus ?case by blast
  qed
qed


lemma is_SDG_path_matched:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'" obtains ns' where "matched n ns' n'" and "set ns \<subseteq> set ns'"
proof(atomize_elim)
  from `n is-ns\<rightarrow>\<^sub>d* n'` show "\<exists>ns'. matched n ns' n' \<and> set ns \<subseteq> set ns'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from `valid_SDG_node n` have "matched n [] n" by(rule matched_Nil)
    thus ?case by fastforce
  next
    case (isSp_Append_cdep n ns n'' n')
    from `\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce intro:intra_SDG_path.intros sum_SDG_edge_valid_SDG_node 
                        sum_SDG_edge_SDG_edge)
    with `matched n ns' n''` have "matched n (ns'@[n'']) n'"
      by(fastforce intro!:matched_Append_intra_SDG_path)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  next
    case (isSp_Append_ddep n ns n'' V n')
    from `\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `n'' \<noteq> n'` have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce intro:intra_SDG_path.intros sum_SDG_edge_valid_SDG_node 
                        sum_SDG_edge_SDG_edge)
    with `matched n ns' n''` have "matched n (ns'@[n'']) n'"
      by(fastforce intro!:matched_Append_intra_SDG_path)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  next
    case (isSp_Append_sum n ns n'' p n')
    from `\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'` obtain ns'' where "matched n'' ns'' n'" and "n'' \<in> set ns''"
      by -(erule sum_SDG_summary_edge_matched)
    with `matched n ns' n''` have "matched n (ns'@ns'') n'" by -(rule matched_Append)
    with `set ns \<subseteq> set ns'` `n'' \<in> set ns''` show ?case by fastforce
  qed
qed


lemma is_SDG_path_intra_CFG_path:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from `n is-ns\<rightarrow>\<^sub>d* n'`
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from `valid_SDG_node n` have "parent_node n -[]\<rightarrow>* parent_node n"
      by(fastforce intro:empty_path valid_SDG_CFG_node)
    thus ?case by(auto simp:intra_path_def)
  next
    case (isSp_Append_cdep n ns n'' n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "n'' \<longrightarrow>\<^bsub>cd\<^esub> n'" by(rule sum_SDG_edge_SDG_edge)
    thus ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with `parent_node n'' = targetnode a` `parent_node n' = sourcenode a'` 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` show ?thesis by fastforce
    qed
  next
    case (isSp_Append_ddep n ns n'' V n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"  by blast
    from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "n'' influences V in n'"
      by(fastforce elim:sum_SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  next
    case (isSp_Append_sum n ns n'' p n')
    from `\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''`
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"  by blast
    from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'` obtain ns' where "matched n'' ns' n'"
      by -(erule sum_SDG_summary_edge_matched)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(erule matched_intra_CFG_path)
    with `parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''` 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce intro:path_Append simp:intra_path_def)
    thus ?case by blast
  qed
qed


text {* SDG paths without return edges *}

inductive intra_call_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ ics-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where icsSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n ics-[]\<rightarrow>\<^sub>d* n"

  | icsSp_Append_cdep:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_ddep:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_sum:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_call:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_param_in:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma ics_SDG_path_valid_SDG_node:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using `n ics-ns\<rightarrow>\<^sub>d* n'`
by(induct rule:intra_call_sum_SDG_path.induct,
   auto intro:sum_SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma ics_SDG_path_Append:
  "\<lbrakk>n'' ics-ns'\<rightarrow>\<^sub>d* n'; n ics-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n ics-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_call_sum_SDG_path.induct,
   auto intro:intra_call_sum_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma is_SDG_path_ics_SDG_path:
  "n is-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n ics-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_sum_SDG_path.induct,auto intro:intra_call_sum_SDG_path.intros)


lemma cc_SDG_path_ics_SDG_path:
  "n cc-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n ics-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:call_cdep_SDG_path.induct,
  auto intro:intra_call_sum_SDG_path.intros SDG_edge_sum_SDG_edge)


lemma ics_SDG_path_split:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" and "n'' \<in> set ns" 
  obtains ns' ns'' where "ns = ns'@ns''" and "n ics-ns'\<rightarrow>\<^sub>d* n''" 
  and "n'' ics-ns''\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from `n ics-ns\<rightarrow>\<^sub>d* n'` `n'' \<in> set ns`
  show "\<exists>ns' ns''. ns = ns'@ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* n'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case icsSp_Nil thus ?case by simp
  next
    case (icsSp_Append_cdep n ns nx n')
    note IH = `n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx`
    from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from `n'' ics-ns''\<rightarrow>\<^sub>d* nx` `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'`
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_cdep)
      with `ns = ns'@ns''` `n ics-ns'\<rightarrow>\<^sub>d* n''` show ?thesis by fastforce
    next
      assume "n'' = nx"
      from `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_cdep)
      with `n ics-ns\<rightarrow>\<^sub>d* nx` `n'' = nx` show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_ddep n ns nx V n')
    note IH = `n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx`
    from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from `n'' ics-ns''\<rightarrow>\<^sub>d* nx` `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `nx \<noteq> n'`
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_ddep)
      with `ns = ns'@ns''` `n ics-ns'\<rightarrow>\<^sub>d* n''` show ?thesis by fastforce
    next
      assume "n'' = nx"
      from `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `nx \<noteq> n'` have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_ddep)
      with `n ics-ns\<rightarrow>\<^sub>d* nx` `n'' = nx` show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_sum n ns nx p n')
    note IH = `n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx`
    from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from `n'' ics-ns''\<rightarrow>\<^sub>d* nx` `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'`
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_sum)
      with `ns = ns'@ns''` `n ics-ns'\<rightarrow>\<^sub>d* n''` show ?thesis by fastforce
    next
      assume "n'' = nx"
      from `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` have "valid_SDG_node nx"
        by(fastforce elim:sum_SDG_edge.cases)
      hence "nx ics-[]\<rightarrow>\<^sub>d* nx" by(fastforce intro:icsSp_Nil)
      with `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_sum)
      with `n ics-ns\<rightarrow>\<^sub>d* nx` `n'' = nx` show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_call n ns nx p n')
    note IH = `n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx`
    from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from `n'' ics-ns''\<rightarrow>\<^sub>d* nx` `nx s-p\<rightarrow>\<^bsub>call\<^esub> n'`
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_call)
      with `ns = ns'@ns''` `n ics-ns'\<rightarrow>\<^sub>d* n''` show ?thesis by fastforce
    next
      assume "n'' = nx"
      from `nx s-p\<rightarrow>\<^bsub>call\<^esub> n'` have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with `nx s-p\<rightarrow>\<^bsub>call\<^esub> n'` have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_call)
      with `n ics-ns\<rightarrow>\<^sub>d* nx` `n'' = nx` show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_param_in n ns nx p V n')
    note IH = `n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx`
    from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from `n'' ics-ns''\<rightarrow>\<^sub>d* nx` `nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'`
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_param_in)
      with `ns = ns'@ns''` `n ics-ns'\<rightarrow>\<^sub>d* n''` show ?thesis by fastforce
    next
      assume "n'' = nx"
      from `nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'` have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with `nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'` have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_param_in)
      with `n ics-ns\<rightarrow>\<^sub>d* nx` `n'' = nx` show ?thesis by fastforce
    qed
  qed
qed


lemma realizable_ics_SDG_path:
  assumes "realizable n ns n'" obtains ns' where "n ics-ns'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from `realizable n ns n'` show "\<exists>ns'. n ics-ns'\<rightarrow>\<^sub>d* n'"
  proof(induct rule:realizable.induct)
    case (realizable_matched n ns n')
    from `matched n ns n'` obtain ns' where "n is-ns'\<rightarrow>\<^sub>d* n'"
      by(erule matched_is_SDG_path)
    thus ?case by(fastforce intro:is_SDG_path_ics_SDG_path)
  next
    case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns' n\<^sub>3)
    from `\<exists>ns'. n\<^sub>0 ics-ns'\<rightarrow>\<^sub>d* n\<^sub>1` obtain nsx where "n\<^sub>0 ics-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    with `n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2` have "n\<^sub>0 ics-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>2"
      by(fastforce intro:SDG_edge_sum_SDG_edge icsSp_Append_call icsSp_Append_param_in)
    from `matched n\<^sub>2 ns' n\<^sub>3` obtain nsx' where "n\<^sub>2 is-nsx'\<rightarrow>\<^sub>d* n\<^sub>3"
      by(erule matched_is_SDG_path)
    hence "n\<^sub>2 ics-nsx'\<rightarrow>\<^sub>d* n\<^sub>3" by(rule is_SDG_path_ics_SDG_path)
    from `n\<^sub>2 ics-nsx'\<rightarrow>\<^sub>d* n\<^sub>3` `n\<^sub>0 ics-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>2`
    have "n\<^sub>0 ics-(nsx@[n\<^sub>1])@nsx'\<rightarrow>\<^sub>d* n\<^sub>3" by(rule ics_SDG_path_Append)
    thus ?case by blast
  qed
qed


lemma ics_SDG_path_realizable:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" 
  obtains ns' where "realizable n ns' n'" and "set ns \<subseteq> set ns'"
proof(atomize_elim)
  from `n ics-ns\<rightarrow>\<^sub>d* n'` show "\<exists>ns'. realizable n ns' n' \<and> set ns \<subseteq> set ns'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case (icsSp_Nil n)
    hence "matched n [] n" by(rule matched_Nil)
    thus ?case by(fastforce intro:realizable_matched)
  next
    case (icsSp_Append_cdep n ns n'' n')
    from `\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' i-[]\<rightarrow>\<^sub>d* n''" by(rule iSp_Nil)
    with `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce elim:iSp_Append_cdep sum_SDG_edge_SDG_edge)
    hence "matched n'' [n''] n'" by(fastforce intro:intra_SDG_path_matched)
    with `realizable n ns' n''` have "realizable n (ns'@[n'']) n'"
      by(rule realizable_Append_matched)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  next
    case (icsSp_Append_ddep n ns n'' V n')
    from `\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "valid_SDG_node n''"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' i-[]\<rightarrow>\<^sub>d* n''" by(rule iSp_Nil)
    with `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `n'' \<noteq> n'` have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce elim:iSp_Append_ddep sum_SDG_edge_SDG_edge)
    hence "matched n'' [n''] n'" by(fastforce intro:intra_SDG_path_matched)
    with `realizable n ns' n''` have "realizable n (ns'@[n'']) n'"
      by(fastforce intro:realizable_Append_matched)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  next
    case (icsSp_Append_sum n ns n'' p n')
    from `\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'` show ?case
    proof(rule sum_edge_cases)
      fix a Q r fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "n'' = CFG_node (sourcenode a)" and "n' = CFG_node (targetnode a')"
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
      have match':"matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
        (CFG_node (sourcenode a'))"
        by(rule intra_proc_matched)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `n'' = CFG_node (sourcenode a)`
      have "n'' -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)"
        by(fastforce intro:SDG_call_edge)
      hence "matched n'' [] n''"
        by(fastforce intro:matched_Nil SDG_edge_valid_SDG_node)
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
        by(rule get_return_edges_valid)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `n' = CFG_node (targetnode a')`
      have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'"
        by(fastforce intro:SDG_return_edge)
      from `matched n'' [] n''` `n'' -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)`
        match' `CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'` `valid_edge a` 
        `a' \<in> get_return_edges a` `n' = CFG_node (targetnode a')` 
        `n'' = CFG_node (sourcenode a)`
      have "matched n'' ([]@n''#[CFG_node (targetnode a)]@[CFG_node (sourcenode a')])
        n'"
        by(fastforce intro:matched_bracket_call)
      with `realizable n ns' n''`
      have "realizable n 
        (ns'@(n''#[CFG_node (targetnode a),CFG_node (sourcenode a')])) n'"
        by(fastforce intro:realizable_Append_matched)
      with `set ns \<subseteq> set ns'` show ?thesis by fastforce
    next
      fix a Q r p fs a' ns'' x x' ins outs
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and match':"matched (Formal_in (targetnode a,x)) ns'' 
                            (Formal_out (sourcenode a',x'))"
        and "n'' = Actual_in (sourcenode a,x)" 
        and "n' = Actual_out (targetnode a',x')" and "(p,ins,outs) \<in> set procs" 
        and "x < length ins" and "x' < length outs"
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `n'' = Actual_in (sourcenode a,x)`
        `(p,ins,outs) \<in> set procs` `x < length ins`
      have "n'' -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)"
        by(fastforce intro!:SDG_param_in_edge)
      hence "matched n'' [] n''" 
        by(fastforce intro:matched_Nil SDG_edge_valid_SDG_node)
      from `valid_edge a` `a' \<in> get_return_edges a` have "valid_edge a'"
        by(rule get_return_edges_valid)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `a' \<in> get_return_edges a`
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from `valid_edge a'` `kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'` `n' = Actual_out (targetnode a',x')`
        `(p,ins,outs) \<in> set procs` `x' < length outs`
      have "Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'"
        by(fastforce intro:SDG_param_out_edge)
      from `matched n'' [] n''` `n'' -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)`
        match' `Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'` `valid_edge a` 
        `a' \<in> get_return_edges a` `n' = Actual_out (targetnode a',x')`
        `n'' = Actual_in (sourcenode a,x)`
      have "matched n'' ([]@n''#ns''@[Formal_out (sourcenode a',x')]) n'"
        by(fastforce intro:matched_bracket_param)
      with `realizable n ns' n''`
      have "realizable n (ns'@(n''#ns''@[Formal_out (sourcenode a',x')])) n'"
        by(fastforce intro:realizable_Append_matched)
      with `set ns \<subseteq> set ns'` show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_call n ns n'' p n')
    from `\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'` have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with `realizable n ns' n''` `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'`
    have "realizable n (ns'@n''#[]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  next
    case (icsSp_Append_param_in n ns n'' p V n')
    from `\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'`
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'` have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with `realizable n ns' n''` `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'`
    have "realizable n (ns'@n''#[]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    with `set ns \<subseteq> set ns'` show ?case by fastforce
  qed
qed



lemma realizable_Append_ics_SDG_path:
  assumes "realizable n ns n''" and "n'' ics-ns'\<rightarrow>\<^sub>d* n'"
  obtains ns'' where "realizable n (ns@ns'') n'"
proof(atomize_elim)
  from `n'' ics-ns'\<rightarrow>\<^sub>d* n'` `realizable n ns n''`
  show "\<exists>ns''. realizable n (ns@ns'') n'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case (icsSp_Nil n'') thus ?case by(rule_tac x="[]" in exI) fastforce
  next
    case (icsSp_Append_cdep n'' ns' nx n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "valid_SDG_node nx" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched nx [] nx" by(rule matched_Nil)
    from `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` `valid_SDG_node nx`
    have "nx i-[]@[nx]\<rightarrow>\<^sub>d* n'" 
      by(fastforce intro:iSp_Append_cdep iSp_Nil sum_SDG_edge_SDG_edge)
    with `matched nx [] nx` have "matched nx ([]@[nx]) n'"
      by(fastforce intro:matched_Append_intra_SDG_path)
    with `realizable n (ns@ns'') nx` have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_ddep n'' ns' nx V n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "valid_SDG_node nx" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched nx [] nx" by(rule matched_Nil)
    from `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `nx \<noteq> n'` `valid_SDG_node nx`
    have "nx i-[]@[nx]\<rightarrow>\<^sub>d* n'" 
      by(fastforce intro:iSp_Append_ddep iSp_Nil sum_SDG_edge_SDG_edge)
    with `matched nx [] nx` have "matched nx ([]@[nx]) n'"
      by(fastforce intro:matched_Append_intra_SDG_path)
    with `realizable n (ns@ns'') nx` have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_sum n'' ns' nx p n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` obtain nsx where "matched nx nsx n'"
      by -(erule sum_SDG_summary_edge_matched)
    with `realizable n (ns@ns'') nx` have "realizable n ((ns@ns'')@nsx) n'"
      by(rule realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_call n'' ns' nx p n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from `nx s-p\<rightarrow>\<^bsub>call\<^esub> n'` have "valid_SDG_node n'" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with `realizable n (ns@ns'') nx` `nx s-p\<rightarrow>\<^bsub>call\<^esub> n'` 
    have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    thus ?case by fastforce
  next
    case (icsSp_Append_param_in n'' ns' nx p V n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from `nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'` have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with `realizable n (ns@ns'') nx` `nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'` 
    have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    thus ?case by fastforce
  qed
qed
      

subsection {* SDG paths without call edges *}

inductive intra_return_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ irs-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where irsSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n irs-[]\<rightarrow>\<^sub>d* n"

  | irsSp_Cons_cdep:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s\<longrightarrow>\<^bsub>cd\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_ddep:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-V\<rightarrow>\<^bsub>dd\<^esub> n''; n \<noteq> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_sum:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p\<rightarrow>\<^bsub>sum\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_return:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p\<rightarrow>\<^bsub>ret\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_param_out:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"



lemma irs_SDG_path_Append:
  "\<lbrakk>n irs-ns\<rightarrow>\<^sub>d* n''; n'' irs-ns'\<rightarrow>\<^sub>d* n'\<rbrakk> \<Longrightarrow> n irs-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_return_sum_SDG_path.induct,
   auto intro:intra_return_sum_SDG_path.intros)


lemma is_SDG_path_irs_SDG_path:
  "n is-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n irs-ns\<rightarrow>\<^sub>d* n'"
proof(induct rule:intra_sum_SDG_path.induct)
  case (isSp_Nil n)
  from `valid_SDG_node n` show ?case by(rule irsSp_Nil)
next
  case (isSp_Append_cdep n ns n'' n')
  from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_cdep irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with `n irs-ns\<rightarrow>\<^sub>d* n''` show ?case by(rule irs_SDG_path_Append)
next
  case (isSp_Append_ddep n ns n'' V n')
  from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `n'' \<noteq> n'` have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_ddep irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with `n irs-ns\<rightarrow>\<^sub>d* n''` show ?case by(rule irs_SDG_path_Append)
next
  case (isSp_Append_sum n ns n'' p n')
  from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'` have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_sum irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with `n irs-ns\<rightarrow>\<^sub>d* n''` show ?case by(rule irs_SDG_path_Append)
qed


lemma irs_SDG_path_split:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n'"
  obtains "n is-ns\<rightarrow>\<^sub>d* n'"
  | nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n irs-nsx\<rightarrow>\<^sub>d* nx"
  and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from `n irs-ns\<rightarrow>\<^sub>d* n'` show "n is-ns\<rightarrow>\<^sub>d* n' \<or>
    (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')"
  proof(induct rule:intra_return_sum_SDG_path.induct)
    case (irsSp_Nil n)
    from `valid_SDG_node n` have "n is-[]\<rightarrow>\<^sub>d* n" by(rule isSp_Nil)
    thus ?case by simp
  next
    case (irsSp_Cons_cdep n'' ns n' n)
    from `n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')`
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from `n s\<longrightarrow>\<^bsub>cd\<^esub> n''` have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_cdep isSp_Nil sum_SDG_edge_valid_SDG_node)
      with `n'' is-ns\<rightarrow>\<^sub>d* n'` have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from `n'' irs-nsx\<rightarrow>\<^sub>d* nx` `n s\<longrightarrow>\<^bsub>cd\<^esub> n''` have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_cdep)
      with `ns = nsx@nx#nsx'` `nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')`
        `nx' is-nsx'\<rightarrow>\<^sub>d* n'`
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_ddep n'' ns n' n V)
    from `n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')`
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from `n s-V\<rightarrow>\<^bsub>dd\<^esub> n''` `n \<noteq> n''` have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_ddep isSp_Nil sum_SDG_edge_valid_SDG_node)
      with `n'' is-ns\<rightarrow>\<^sub>d* n'` have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'.  ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from `n'' irs-nsx\<rightarrow>\<^sub>d* nx` `n s-V\<rightarrow>\<^bsub>dd\<^esub> n''` `n \<noteq> n''` have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_ddep)
      with `ns = nsx@nx#nsx'` `nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')`
        `nx' is-nsx'\<rightarrow>\<^sub>d* n'`
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_sum n'' ns n' n p)
    from `n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')`
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from `n s-p\<rightarrow>\<^bsub>sum\<^esub> n''` have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_sum isSp_Nil sum_SDG_edge_valid_SDG_node)
      with `n'' is-ns\<rightarrow>\<^sub>d* n'` have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')" 
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from `n'' irs-nsx\<rightarrow>\<^sub>d* nx` `n s-p\<rightarrow>\<^bsub>sum\<^esub> n''` have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_sum)
      with `ns = nsx@nx#nsx'` `nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')`
        `nx' is-nsx'\<rightarrow>\<^sub>d* n'`
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_return n'' ns n' n p)
    from `n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')`
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from `n s-p\<rightarrow>\<^bsub>ret\<^esub> n''` have "valid_SDG_node n" by(rule sum_SDG_edge_valid_SDG_node)
      hence "n irs-[]\<rightarrow>\<^sub>d* n" by(rule irsSp_Nil)
      with `n s-p\<rightarrow>\<^bsub>ret\<^esub> n''` `n'' is-ns\<rightarrow>\<^sub>d* n'` show ?thesis by fastforce
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')"
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from `n'' irs-nsx\<rightarrow>\<^sub>d* nx` `n s-p\<rightarrow>\<^bsub>ret\<^esub> n''` have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_return)
      with `ns = nsx@nx#nsx'` `nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')`
        `nx' is-nsx'\<rightarrow>\<^sub>d* n'`
      show ?thesis by fastforce
    qed
  next
    case (irsSp_Cons_param_out n'' ns n' n p V)
    from `n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')`
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from `n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''` have "valid_SDG_node n"
        by(rule sum_SDG_edge_valid_SDG_node)
      hence "n irs-[]\<rightarrow>\<^sub>d* n" by(rule irsSp_Nil)
      with `n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''` `n'' is-ns\<rightarrow>\<^sub>d* n'` show ?thesis by fastforce
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')" 
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from `n'' irs-nsx\<rightarrow>\<^sub>d* nx` `n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''` have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_param_out)
      with `ns = nsx@nx#nsx'` `nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')`
        `nx' is-nsx'\<rightarrow>\<^sub>d* n'`
      show ?thesis by fastforce
    qed
  qed
qed


lemma irs_SDG_path_matched:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n''" and "n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
  obtains nx nsx where "matched nx nsx n'" and "n \<in> set nsx" 
  and "nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
proof(atomize_elim)
  from assms
  show "\<exists>nx nsx. matched nx nsx n' \<and> n \<in> set nsx \<and> 
                 nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
  proof(induct ns arbitrary:n'' n' p V rule:length_induct)
    fix ns n'' n' p V
    assume IH:"\<forall>ns'. length ns' < length ns \<longrightarrow>
      (\<forall>n''. n irs-ns'\<rightarrow>\<^sub>d* n'' \<longrightarrow> 
      (\<forall>nx' p' V'. (n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> n'' s-p':V'\<rightarrow>\<^bsub>out\<^esub> nx') \<longrightarrow> 
        (\<exists>nx nsx. matched nx nsx nx' \<and> n \<in> set nsx \<and> 
                  nx s-p'\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx'))))"
      and "n irs-ns\<rightarrow>\<^sub>d* n''" and "n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
    from `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'` have "valid_SDG_node n''"
      by(fastforce intro:sum_SDG_edge_valid_SDG_node)
    from `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'`
    have "n'' -p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' -p:V\<rightarrow>\<^bsub>out\<^esub> n'"
      by(fastforce intro:sum_SDG_edge_SDG_edge SDG_edge_sum_SDG_edge)
    from `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'`
    have "CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')"
      by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
    then obtain a Q f where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "parent_node n'' = sourcenode a" and "parent_node n' = targetnode a"
      by(fastforce elim:sum_SDG_edge.cases)
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain a' Q' r' fs' 
      where "a \<in> get_return_edges a'" and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
      by(erule return_edge_determines_call_and_sum_edge)
    from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
    have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
      by(fastforce intro:sum_SDG_call_edge)
    from `CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` 
    have "get_proc (parent_node n'') = p"
      by(auto elim!:sum_SDG_edge.cases intro:get_proc_return)
    from `n irs-ns\<rightarrow>\<^sub>d* n''`
    show "\<exists>nx nsx. matched nx nsx n' \<and> n \<in> set nsx \<and> 
                   nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
    proof(rule irs_SDG_path_split)
      assume "n is-ns\<rightarrow>\<^sub>d* n''"
      hence "valid_SDG_node n" by(rule is_SDG_path_valid_SDG_node)
      then obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* parent_node n"
        by(fastforce dest:valid_SDG_CFG_node Entry_path)
      then obtain asx' where "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n"
        and "\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
        by -(erule valid_Entry_path_ascending_path)
      from `n is-ns\<rightarrow>\<^sub>d* n''` obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"
        by(erule is_SDG_path_CFG_path)
      hence "get_proc (parent_node n) = get_proc (parent_node n'')"
        by(rule intra_path_get_procs)
      from `valid_SDG_node n` have "valid_node (parent_node n)"
        by(rule valid_SDG_CFG_node)
      hence "valid_SDG_node (CFG_node (parent_node n))" by simp
      have "\<exists>a as. valid_edge a \<and> (\<exists>Q p r fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
        targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n"
      proof(cases "\<forall>a' \<in> set asx'. intra_kind(kind a')")
        case True
        with `(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n`
        have "(_Entry_) -asx'\<rightarrow>\<^sub>\<iota>* parent_node n"
          by(fastforce simp:intra_path_def vp_def)
        hence "get_proc (_Entry_) = get_proc (parent_node n)"
          by(rule intra_path_get_procs)
        with get_proc_Entry have "get_proc (parent_node n) = Main" by simp
        from `get_proc (parent_node n) = get_proc (parent_node n'')`
          `get_proc (parent_node n) = Main` 
        have "get_proc (parent_node n'') = Main" by simp
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "get_proc (sourcenode a) = p"
          by(rule get_proc_return)
        with `parent_node n'' = sourcenode a` `get_proc (parent_node n'') = Main`
        have "p = Main" by simp
        with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with `valid_edge a` have False by(rule Main_no_return_source)
        thus ?thesis by simp
      next
        assume "\<not> (\<forall>a'\<in>set asx'. intra_kind (kind a'))"
        with `\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
        have "\<exists>a' \<in> set asx'. \<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          by(fastforce simp:intra_kind_def)
        then obtain as a' as' where "asx' = as@a'#as'" 
          and "\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
          and "\<forall>a' \<in> set as'. \<not> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by(erule split_list_last_propE)
        with `\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
        have "\<forall>a'\<in>set as'. intra_kind (kind a')" by(auto simp:intra_kind_def)
        from `(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n` `asx' = as@a'#as'`
        have "valid_edge a'" and "targetnode a' -as'\<rightarrow>* parent_node n"
          by(auto dest:path_split simp:vp_def)
        with `\<forall>a'\<in>set as'. intra_kind (kind a')` `\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        show ?thesis by(fastforce simp:intra_path_def)
      qed
      then obtain ax asx Qx rx fsx px where "valid_edge ax"
        and "kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx" and "targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n"
        by blast
      from `valid_edge ax` `kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx` 
      have "get_proc (targetnode ax) = px"
        by(rule get_proc_call)
      from `targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n` 
      have "get_proc (targetnode ax) = get_proc (parent_node n)" 
        by(rule intra_path_get_procs)
      with `get_proc (parent_node n) = get_proc (parent_node n'')` 
        `get_proc (targetnode ax) = px`
      have "get_proc (parent_node n'') = px" by simp
      with `get_proc (parent_node n'') = p` have [simp]:"px = p" by simp
      from `valid_edge a'` `valid_edge ax` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
        `kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx`
      have "targetnode a' = targetnode ax" by simp(rule same_proc_call_unique_target)
      have "parent_node n \<noteq> (_Exit_)"
      proof
        assume "parent_node n = (_Exit_)"
        from `n is-ns\<rightarrow>\<^sub>d* n''` obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"
          by(erule is_SDG_path_CFG_path)
        with `parent_node n = (_Exit_)`
        have "(_Exit_) -as\<rightarrow>* parent_node n''" by(simp add:intra_path_def)
        hence "parent_node n'' = (_Exit_)" by(fastforce dest:path_Exit_source)
        from `get_proc (parent_node n'') = p` `parent_node n'' = (_Exit_)`
          `parent_node n'' = sourcenode a` get_proc_Exit 
        have "p = Main" by simp
        with `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with `valid_edge a` show False by(rule Main_no_return_source)
      qed
      have "\<exists>nsx. CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
      proof(cases "targetnode a' = parent_node n")
        case True
        with `valid_SDG_node (CFG_node (parent_node n))` 
        have "CFG_node (targetnode a') cd-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
          by(fastforce intro:cdSp_Nil)
        thus ?thesis by blast
      next
        case False
        with `targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n` `parent_node n \<noteq> (_Exit_)`
          `valid_edge ax` `kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx` `targetnode a' = targetnode ax`
        obtain nsx 
          where "CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
          by(fastforce elim!:in_proc_cdep_SDG_path)
        thus ?thesis by blast
      qed
      then obtain nsx 
        where "CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)" by blast
      hence "CFG_node (targetnode a') i-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
        by(rule cdep_SDG_path_intra_SDG_path)
      show ?thesis
      proof(cases ns)
        case Nil
        with `n is-ns\<rightarrow>\<^sub>d* n''` have "n = n''"
          by(fastforce elim:intra_sum_SDG_path.cases)
        from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `a \<in> get_return_edges a'`
        have "matched (CFG_node (targetnode a')) [CFG_node (targetnode a')]
          (CFG_node (sourcenode a))" by(rule intra_proc_matched)
        from `valid_SDG_node n''`
        have "n'' = CFG_node (parent_node n'') \<or> CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''"
          by(rule valid_SDG_node_cases)
        hence "\<exists>nsx. CFG_node (parent_node n'') i-nsx\<rightarrow>\<^sub>d* n''"
        proof
          assume "n'' = CFG_node (parent_node n'')"
          with `valid_SDG_node n''` have "CFG_node (parent_node n'') i-[]\<rightarrow>\<^sub>d* n''"
            by(fastforce intro:iSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''"
          from `valid_SDG_node n''` have "valid_node (parent_node n'')"
            by(rule valid_SDG_CFG_node)
          hence "valid_SDG_node (CFG_node (parent_node n''))" by simp
          hence "CFG_node (parent_node n'') i-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n'')"
            by(rule iSp_Nil)
          with `CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''`
          have "CFG_node (parent_node n'') i-[]@[CFG_node (parent_node n'')]\<rightarrow>\<^sub>d* n''"
            by(fastforce intro:iSp_Append_cdep sum_SDG_edge_SDG_edge)
          thus ?thesis by blast
        qed
        with `parent_node n'' = sourcenode a`
        obtain nsx where "CFG_node (sourcenode a) i-nsx\<rightarrow>\<^sub>d* n''" by fastforce
        with `matched (CFG_node (targetnode a')) [CFG_node (targetnode a')]
          (CFG_node (sourcenode a))`
        have "matched (CFG_node (targetnode a')) ([CFG_node (targetnode a')]@nsx) n''"
          by(fastforce intro:matched_Append intra_SDG_path_matched)
        moreover
        from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
        have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
          by(fastforce intro:SDG_call_edge)
        moreover
        from `valid_edge a'` have "valid_SDG_node (CFG_node (sourcenode a'))"
          by simp
        hence "matched (CFG_node (sourcenode a')) [] (CFG_node (sourcenode a'))"
          by(rule matched_Nil)
        ultimately have "matched (CFG_node (sourcenode a'))
          ([]@(CFG_node (sourcenode a'))#([CFG_node (targetnode a')]@nsx)@[n'']) n'"
          using `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'` `parent_node n' = targetnode a`
            `parent_node n'' = sourcenode a` `valid_edge a'` `a \<in> get_return_edges a'`
          by(fastforce intro:matched_bracket_call dest:sum_SDG_edge_SDG_edge)
        with `n = n''` `CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)`
          `parent_node n' = targetnode a`
        show ?thesis by fastforce
      next
        case Cons
        with `n is-ns\<rightarrow>\<^sub>d* n''` have "n \<in> set ns"
          by(induct rule:intra_sum_SDG_path_rev_induct) auto
        from `n is-ns\<rightarrow>\<^sub>d* n''` obtain ns' where "matched n ns' n''" 
          and "set ns \<subseteq> set ns'" by(erule is_SDG_path_matched)
        with `n \<in> set ns` have "n \<in> set ns'" by fastforce
        from `valid_SDG_node n`
        have "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
          by(rule valid_SDG_node_cases)
        hence "\<exists>nsx. CFG_node (parent_node n) i-nsx\<rightarrow>\<^sub>d* n"
        proof
          assume "n = CFG_node (parent_node n)"
          with `valid_SDG_node n` have "CFG_node (parent_node n) i-[]\<rightarrow>\<^sub>d* n"
            by(fastforce intro:iSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
          from `valid_SDG_node (CFG_node (parent_node n))` 
          have "CFG_node (parent_node n) i-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
            by(rule iSp_Nil)
          with `CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n`
          have "CFG_node (parent_node n) i-[]@[CFG_node (parent_node n)]\<rightarrow>\<^sub>d* n"
            by(fastforce intro:iSp_Append_cdep sum_SDG_edge_SDG_edge)
          thus ?thesis by blast
        qed
        then obtain nsx' where "CFG_node (parent_node n) i-nsx'\<rightarrow>\<^sub>d* n" by blast
        with `CFG_node (targetnode a') i-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)`
        have "CFG_node (targetnode a') i-nsx@nsx'\<rightarrow>\<^sub>d* n"
          by -(rule intra_SDG_path_Append)
        hence "matched (CFG_node (targetnode a')) (nsx@nsx') n"
          by(rule intra_SDG_path_matched)
        with `matched n ns' n''` 
        have "matched (CFG_node (targetnode a')) ((nsx@nsx')@ns') n''"
          by(rule matched_Append)
        moreover
        from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
        have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
          by(fastforce intro:SDG_call_edge)
        moreover
        from `valid_edge a'` have "valid_SDG_node (CFG_node (sourcenode a'))"
          by simp
        hence "matched (CFG_node (sourcenode a')) [] (CFG_node (sourcenode a'))"
          by(rule matched_Nil)
        ultimately have "matched (CFG_node (sourcenode a')) 
          ([]@(CFG_node (sourcenode a'))#((nsx@nsx')@ns')@[n'']) n'"
          using  `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'` `parent_node n' = targetnode a`
            `parent_node n'' = sourcenode a` `valid_edge a'` `a \<in> get_return_edges a'`
          by(fastforce intro:matched_bracket_call dest:sum_SDG_edge_SDG_edge)
        with `CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)`
          `parent_node n' = targetnode a` `n \<in> set ns'`
        show ?thesis by fastforce
      qed
    next
      fix ms ms' m m' px
      assume "ns = ms@m#ms'" and "n irs-ms\<rightarrow>\<^sub>d* m"
        and "m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')" and "m' is-ms'\<rightarrow>\<^sub>d* n''"
      from `ns = ms@m#ms'` have "length ms < length ns" by simp
      with IH `n irs-ms\<rightarrow>\<^sub>d* m` `m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')` obtain mx msx
        where "matched mx msx m'" and "n \<in> set msx" 
        and "mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')" by fastforce
      from `m' is-ms'\<rightarrow>\<^sub>d* n''` obtain msx' where "matched m' msx' n''"
        by -(erule is_SDG_path_matched)
      with `matched mx msx m'` have "matched mx (msx@msx') n''"
        by -(rule matched_Append)
      from `m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')`
      have "m -px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m -px:V\<rightarrow>\<^bsub>out\<^esub> m')"
        by(auto intro:sum_SDG_edge_SDG_edge SDG_edge_sum_SDG_edge)
      from `m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')`
      have "CFG_node (parent_node m) s-px\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node m')"
        by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
      then obtain ax Qx fx where "valid_edge ax" and "kind ax = Qx\<hookleftarrow>\<^bsub>px\<^esub>fx"
      and "parent_node m = sourcenode ax" and "parent_node m' = targetnode ax"
        by(fastforce elim:sum_SDG_edge.cases)
      from `valid_edge ax` `kind ax = Qx\<hookleftarrow>\<^bsub>px\<^esub>fx` obtain ax' Qx' rx' fsx' 
        where "ax \<in> get_return_edges ax'" and "valid_edge ax'" 
        and "kind ax' = Qx':rx'\<hookrightarrow>\<^bsub>px\<^esub>fsx'"
        and "CFG_node (sourcenode ax') s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode ax)"
        by(erule return_edge_determines_call_and_sum_edge)
      from `valid_edge ax'` `kind ax' = Qx':rx'\<hookrightarrow>\<^bsub>px\<^esub>fsx'`
      have "CFG_node (sourcenode ax') s-px\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode ax')"
        by(fastforce intro:sum_SDG_call_edge)
      from `mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')`
      have "valid_SDG_node mx" by(rule sum_SDG_edge_valid_SDG_node)
      have "\<exists>msx''. CFG_node (targetnode a') cd-msx''\<rightarrow>\<^sub>d* mx"
      proof(cases "targetnode a' = parent_node mx")
        case True
        from `valid_SDG_node mx` 
        have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
          by(rule valid_SDG_node_cases)
        thus ?thesis
        proof
          assume "mx = CFG_node (parent_node mx)"
          with `valid_SDG_node mx` True
          have "CFG_node (targetnode a') cd-[]\<rightarrow>\<^sub>d* mx" by(fastforce intro:cdSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
          with `valid_edge a'` True[THEN sym]
          have "CFG_node (targetnode a') cd-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* mx"
            by(fastforce intro:cdep_SDG_path.intros)
          thus ?thesis by blast
        qed
      next
        case False
        show ?thesis
        proof(cases "\<forall>ai. valid_edge ai \<and> sourcenode ai = parent_node mx
            \<longrightarrow> ai \<notin> get_return_edges a'")
          case True
          { assume "parent_node mx = (_Exit_)"
            with `mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')`
            obtain ai where "valid_edge ai" and "sourcenode ai = (_Exit_)"
              by -(erule sum_SDG_edge.cases,auto)
            hence False by(rule Exit_source) }
          hence "parent_node mx \<noteq> (_Exit_)" by fastforce
          from `valid_SDG_node mx` have "valid_node (parent_node mx)"
            by(rule valid_SDG_CFG_node)
          then obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* parent_node mx"
            by(fastforce intro:Entry_path)
          then obtain asx' where "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx"
            and "\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by -(erule valid_Entry_path_ascending_path)
          from `mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')`
          obtain nsi where "matched mx nsi (CFG_node (parent_node m'))"
            by -(erule sum_SDG_summary_edge_matched)
          then obtain asi where "parent_node mx -asi\<rightarrow>\<^bsub>sl\<^esub>* parent_node m'"
            by(fastforce elim:matched_same_level_CFG_path)
          hence "get_proc (parent_node mx) = get_proc (parent_node m')"
            by(rule slp_get_proc)
          from `m' is-ms'\<rightarrow>\<^sub>d* n''` obtain nsi' where "matched m' nsi' n''"
            by -(erule is_SDG_path_matched)
          then obtain asi' where "parent_node m' -asi'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''"
            by -(erule matched_same_level_CFG_path)
          hence "get_proc (parent_node m') = get_proc (parent_node n'')"
            by(rule slp_get_proc)
          with `get_proc (parent_node mx) = get_proc (parent_node m')`
          have "get_proc (parent_node mx) = get_proc (parent_node n'')" by simp
          from `get_proc (parent_node n'') = p` 
            `get_proc (parent_node mx) = get_proc (parent_node n'')`
          have "get_proc (parent_node mx) = p" by simp
          have "\<exists>asx. targetnode a' -asx\<rightarrow>\<^sub>\<iota>* parent_node mx"
          proof(cases "\<forall>a' \<in> set asx'. intra_kind(kind a')")
            case True
            with `(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx` 
            have "(_Entry_) -asx'\<rightarrow>\<^sub>\<iota>* parent_node mx"
              by(simp add:vp_def intra_path_def)
            hence "get_proc (_Entry_) = get_proc (parent_node mx)"
              by(rule intra_path_get_procs)
            with `get_proc (parent_node mx) = p` have "get_proc (_Entry_) = p"
              by simp
            with `CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')`
            have False
              by -(erule sum_SDG_edge.cases,
                auto intro:Main_no_return_source simp:get_proc_Entry)
            thus ?thesis by simp
          next
            case False
            hence "\<exists>a' \<in> set asx'. \<not> intra_kind (kind a')" by fastforce
            then obtain ai as' as'' where "asx' = as'@ai#as''" 
              and "\<not> intra_kind (kind ai)" and "\<forall>a' \<in> set as''. intra_kind (kind a')"
              by(fastforce elim!:split_list_last_propE)
            from `asx' = as'@ai#as''` `\<not> intra_kind (kind ai)`
              `\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)`
            obtain Qi ri pi fsi where "kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi" 
              and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> 
              (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
              by auto
            from `(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx` `asx' = as'@ai#as''`
              `\<forall>a' \<in> set as''. intra_kind (kind a')`
            have "valid_edge ai" and "targetnode ai -as''\<rightarrow>\<^sub>\<iota>* parent_node mx"
              by(auto intro:path_split simp:vp_def intra_path_def)
            hence "get_proc (targetnode ai) = get_proc (parent_node mx)"
              by -(rule intra_path_get_procs)
            with `get_proc (parent_node mx) = p` `valid_edge ai`
              `kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi`
            have [simp]:"pi = p" by(fastforce dest:get_proc_call)
            from `valid_edge ai` `valid_edge a'` 
              `kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
            have "targetnode ai = targetnode a'" 
              by(fastforce intro:same_proc_call_unique_target)
            with `targetnode ai -as''\<rightarrow>\<^sub>\<iota>* parent_node mx`
            show ?thesis by fastforce
          qed
          then obtain asx where "targetnode a' -asx\<rightarrow>\<^sub>\<iota>* parent_node mx" by blast
          from this `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
            `parent_node mx \<noteq> (_Exit_)` `targetnode a' \<noteq> parent_node mx` True
          obtain msi 
            where "CFG_node(targetnode a') cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)"
            by(fastforce elim!:in_proc_cdep_SDG_path)
          from `valid_SDG_node mx` 
          have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "mx = CFG_node (parent_node mx)"
            with `CFG_node(targetnode a')cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)`
            show ?thesis by fastforce
          next
            assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            with `CFG_node(targetnode a')cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)`
            have "CFG_node(targetnode a') cd-msi@[CFG_node(parent_node mx)]\<rightarrow>\<^sub>d* mx"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        next
          case False
          then obtain ai where "valid_edge ai" and "sourcenode ai = parent_node mx"
            and "ai \<in> get_return_edges a'" by blast
          with `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
          have "CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (parent_node mx)"
            by(auto intro:SDG_proc_entry_exit_cdep)       
          with `valid_edge a'` 
          have cd_path:"CFG_node (targetnode a') cd-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
                        CFG_node (parent_node mx)"
            by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
          from `valid_SDG_node mx` 
          have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "mx = CFG_node (parent_node mx)"
            with cd_path show ?thesis by fastforce
          next
            assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            with cd_path have "CFG_node (targetnode a') 
              cd-[CFG_node (targetnode a')]@[CFG_node (parent_node mx)]\<rightarrow>\<^sub>d* mx"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        qed
      qed
      then obtain msx'' 
        where "CFG_node (targetnode a') cd-msx''\<rightarrow>\<^sub>d* mx" by blast
      hence "CFG_node (targetnode a') i-msx''\<rightarrow>\<^sub>d* mx"
        by(rule cdep_SDG_path_intra_SDG_path)
      with `valid_edge a'` 
      have "matched (CFG_node (targetnode a')) ([]@msx'') mx"
        by(fastforce intro:matched_Append_intra_SDG_path matched_Nil)
      with `matched mx (msx@msx') n''`
      have "matched (CFG_node (targetnode a')) (msx''@(msx@msx')) n''"
        by(fastforce intro:matched_Append)
      with `valid_edge a'` `CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')`
        `n'' -p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' -p:V\<rightarrow>\<^bsub>out\<^esub> n'` `a \<in> get_return_edges a'`
        `parent_node n'' = sourcenode a` `parent_node n' = targetnode a`
      have "matched (CFG_node (sourcenode a')) 
        ([]@CFG_node (sourcenode a')#(msx''@(msx@msx'))@[n'']) n'"
        by(fastforce intro:matched_bracket_call matched_Nil sum_SDG_edge_SDG_edge)
      with `n \<in> set msx` `CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)`
        `parent_node n' = targetnode a`
      show ?thesis by fastforce
    qed
  qed
qed


lemma irs_SDG_path_realizable:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n'" and "n \<noteq> n'"
  obtains ns' where "realizable (CFG_node (_Entry_)) ns' n'" and "n \<in> set ns'"
proof(atomize_elim)
  from `n irs-ns\<rightarrow>\<^sub>d* n'`
  have "n = n' \<or> (\<exists>ns'. realizable (CFG_node (_Entry_)) ns' n' \<and> n \<in> set ns')"
  proof(rule irs_SDG_path_split)
    assume "n is-ns\<rightarrow>\<^sub>d* n'"
    show ?thesis
    proof(cases "ns = []")
      case True
      with `n is-ns\<rightarrow>\<^sub>d* n'` have "n = n'" by(fastforce elim:intra_sum_SDG_path.cases)
      thus ?thesis by simp
    next
      case False
      with `n is-ns\<rightarrow>\<^sub>d* n'` have "n \<in> set ns" by(fastforce dest:is_SDG_path_hd)
      from `n is-ns\<rightarrow>\<^sub>d* n'` have "valid_SDG_node n" and "valid_SDG_node n'"
        by(rule is_SDG_path_valid_SDG_node)+
      hence "valid_node (parent_node n)" by -(rule valid_SDG_CFG_node)
      from `n is-ns\<rightarrow>\<^sub>d* n'` obtain ns' where "matched n ns' n'" and "set ns \<subseteq> set ns'"
        by(erule is_SDG_path_matched)
      with `n \<in> set ns` have "n \<in> set ns'" by fastforce
      from `valid_node (parent_node n)`
      show ?thesis
      proof(cases "parent_node n = (_Exit_)")
        case True
        with `valid_SDG_node n` have "n = CFG_node (_Exit_)"
          by(rule valid_SDG_node_parent_Exit)
        from `n is-ns\<rightarrow>\<^sub>d* n'` obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by -(erule is_SDG_path_intra_CFG_path)
        with `n = CFG_node (_Exit_)` have "parent_node n' = (_Exit_)"
          by(fastforce dest:path_Exit_source simp:intra_path_def)
        with `valid_SDG_node n'` have "n' = CFG_node (_Exit_)"
          by(rule valid_SDG_node_parent_Exit)
        with `n = CFG_node (_Exit_)` show ?thesis by simp
      next
        case False
        with `valid_SDG_node n`
        obtain nsx where "CFG_node (_Entry_) cc-nsx\<rightarrow>\<^sub>d* n"
          by(erule Entry_cc_SDG_path_to_inner_node)
        hence "realizable (CFG_node (_Entry_)) nsx n" 
          by(rule cdep_SDG_path_realizable)
        with `matched n ns' n'`
        have "realizable (CFG_node (_Entry_)) (nsx@ns') n'"
          by -(rule realizable_Append_matched)
        with `n \<in> set ns'` show ?thesis by fastforce
      qed
    qed
  next
    fix nsx nsx' nx nx' p
    assume "ns = nsx@nx#nsx'" and "n irs-nsx\<rightarrow>\<^sub>d* nx"
      and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'"
    from `nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')`
    have "CFG_node (parent_node nx) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')"
      by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
    then obtain a Q f where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "parent_node nx = sourcenode a" and "parent_node nx' = targetnode a"
      by(fastforce elim:sum_SDG_edge.cases)
    from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` obtain a' Q' r' fs' 
      where "a \<in> get_return_edges a'" and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
      by(erule return_edge_determines_call_and_sum_edge)
    from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'`
    have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
      by(fastforce intro:sum_SDG_call_edge)
    from `n irs-nsx\<rightarrow>\<^sub>d* nx` `nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')`
    obtain m ms where "matched m ms nx'" and "n \<in> set ms"
      and "m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')"
      by(fastforce elim:irs_SDG_path_matched)
    from `nx' is-nsx'\<rightarrow>\<^sub>d* n'` obtain ms' where "matched nx' ms' n'" 
      and "set nsx' \<subseteq> set ms'" by(erule is_SDG_path_matched)
    with `matched m ms nx'` have "matched m (ms@ms') n'" by -(rule matched_Append)
   from `m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')` have "valid_SDG_node m"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "valid_node (parent_node m)" by(rule valid_SDG_CFG_node)
    thus ?thesis
    proof(cases "parent_node m = (_Exit_)")
      case True
      from `m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')` obtain a where "valid_edge a" 
        and "sourcenode a = parent_node m"
        by(fastforce elim:sum_SDG_edge.cases)
      with True have False by -(rule Exit_source,simp_all)
      thus ?thesis by simp
    next
      case False
      with `valid_SDG_node m`
      obtain ms'' where "CFG_node (_Entry_) cc-ms''\<rightarrow>\<^sub>d* m"
        by(erule Entry_cc_SDG_path_to_inner_node)
      hence "realizable (CFG_node (_Entry_)) ms'' m" 
        by(rule cdep_SDG_path_realizable)
      with `matched m (ms@ms') n'`
      have "realizable (CFG_node (_Entry_)) (ms''@(ms@ms')) n'"
        by -(rule realizable_Append_matched)
      with `n \<in> set ms` show ?thesis by fastforce
    qed
  qed
  with `n \<noteq> n'` show "\<exists>ns'. realizable (CFG_node (_Entry_)) ns' n' \<and> n \<in> set ns'"
    by simp
qed

end

end
