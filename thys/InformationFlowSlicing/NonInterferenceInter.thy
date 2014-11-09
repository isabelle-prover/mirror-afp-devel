section {* HRB Slicing guarantees IFC Noninterference *}

theory NonInterferenceInter 
  imports "../HRB-Slicing/StaticInter/FundamentalProperty"
begin

subsection {* Assumptions of this Approach *}

text {*
Classical IFC noninterference, a special case of a noninterference
definition using partial equivalence relations (per)
\cite{SabelfeldS:01}, partitions the variables (i.e.\ locations) into
security levels. Usually, only levels for secret or high, written
@{text H}, and public or low, written @{text L}, variables are
used. Basically, a program that is noninterferent has to fulfil one
basic property: executing the program in two different initial states
that may differ in the values of their @{text H}-variables yields two
final states that again only differ in the values of their 
@{text H}-variables; thus the values of the @{text H}-variables did not
influence those of the @{text L}-variables.

Every per-based approach makes certain
assumptions: (i) all \mbox{@{text H}-variables} are defined at the
beginning of the program, (ii) all @{text L}-variables are observed (or
used in our terms) at the end and (iii) every variable is either
@{text H} or @{text L}. This security label is fixed for a variable
and can not be altered during a program run. Thus, we have to extend 
the prerequisites of the slicing framework in \cite{Wasserrab:09} accordingly
in a new locale:

*}

locale NonInterferenceInterGraph =
  SDG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses 
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list" +
  fixes H :: "'var set"
  fixes L :: "'var set"
  fixes High :: "'node"  ("'('_High'_')")
  fixes Low :: "'node"   ("'('_Low'_')")
  assumes Entry_edge_Exit_or_High:
  "\<lbrakk>valid_edge a; sourcenode a = (_Entry_)\<rbrakk> 
    \<Longrightarrow> targetnode a = (_Exit_) \<or> targetnode a = (_High_)"
  and High_target_Entry_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Entry_) \<and> targetnode a = (_High_) \<and>
       kind a = (\<lambda>s. True)\<^sub>\<surd>"
  and Entry_predecessor_of_High:
  "\<lbrakk>valid_edge a; targetnode a = (_High_)\<rbrakk> \<Longrightarrow> sourcenode a = (_Entry_)"
  and Exit_edge_Entry_or_Low: "\<lbrakk>valid_edge a; targetnode a = (_Exit_)\<rbrakk> 
    \<Longrightarrow> sourcenode a = (_Entry_) \<or> sourcenode a = (_Low_)"
  and Low_source_Exit_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Low_) \<and> targetnode a = (_Exit_) \<and> 
       kind a = (\<lambda>s. True)\<^sub>\<surd>"
  and Exit_successor_of_Low:
  "\<lbrakk>valid_edge a; sourcenode a = (_Low_)\<rbrakk> \<Longrightarrow> targetnode a = (_Exit_)"
  and DefHigh: "Def (_High_) = H" 
  and UseHigh: "Use (_High_) = H"
  and UseLow: "Use (_Low_) = L"
  and HighLowDistinct: "H \<inter> L = {}"
  and HighLowUNIV: "H \<union> L = UNIV"

begin

lemma Low_neq_Exit: assumes "L \<noteq> {}" shows "(_Low_) \<noteq> (_Exit_)"
proof
  assume "(_Low_) = (_Exit_)"
  have "Use (_Exit_) = {}" by fastforce
  with UseLow `L \<noteq> {}` `(_Low_) = (_Exit_)` show False by simp
qed


lemma valid_node_High [simp]:"valid_node (_High_)"
  using High_target_Entry_edge by fastforce

lemma valid_node_Low [simp]:"valid_node (_Low_)"
  using Low_source_Exit_edge by fastforce


lemma get_proc_Low:
  "get_proc (_Low_) = Main"
proof -
  from Low_source_Exit_edge obtain a where "valid_edge a"
    and "sourcenode a = (_Low_)" and "targetnode a = (_Exit_)"
    and "intra_kind (kind a)" by(fastforce simp:intra_kind_def)
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with `sourcenode a = (_Low_)` `targetnode a = (_Exit_)` get_proc_Exit
  show ?thesis by simp
qed

lemma get_proc_High:
  "get_proc (_High_) = Main"
proof -
  from High_target_Entry_edge obtain a where "valid_edge a"
    and "sourcenode a = (_Entry_)" and "targetnode a = (_High_)"
    and "intra_kind (kind a)" by(fastforce simp:intra_kind_def)
  from `valid_edge a` `intra_kind (kind a)`
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with `sourcenode a = (_Entry_)` `targetnode a = (_High_)` get_proc_Entry
  show ?thesis by simp
qed



lemma Entry_path_High_path:
  assumes "(_Entry_) -as\<rightarrow>* n" and "inner_node n"
  obtains a' as' where "as = a'#as'" and "(_High_) -as'\<rightarrow>* n" 
  and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
proof(atomize_elim)
  from `(_Entry_) -as\<rightarrow>* n` `inner_node n`
  show "\<exists>a' as'. as = a'#as' \<and> (_High_) -as'\<rightarrow>* n \<and> kind a' = (\<lambda>s. True)\<^sub>\<surd>"
  proof(induct n'\<equiv>"(_Entry_)" as n rule:path.induct)
    case (Cons_path n'' as n' a)
    from `n'' -as\<rightarrow>* n'` `inner_node n'` have "n'' \<noteq> (_Exit_)" 
      by(fastforce simp:inner_node_def)
    with `valid_edge a` `sourcenode a = (_Entry_)` `targetnode a = n''`
    have "n'' = (_High_)" by -(drule Entry_edge_Exit_or_High,auto)
    from High_target_Entry_edge
    obtain a' where "valid_edge a'" and "sourcenode a' = (_Entry_)"
      and "targetnode a' = (_High_)" and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
      by blast
    with `valid_edge a` `sourcenode a = (_Entry_)` `targetnode a = n''`
      `n'' = (_High_)`
    have "a = a'" by(auto dest:edge_det)
    with `n'' -as\<rightarrow>* n'` `n'' = (_High_)` `kind a' = (\<lambda>s. True)\<^sub>\<surd>` show ?case by blast
  qed fastforce
qed


lemma Exit_path_Low_path:
  assumes "n -as\<rightarrow>* (_Exit_)" and "inner_node n"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* (_Low_)"
  and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
proof(atomize_elim)
  from `n -as\<rightarrow>* (_Exit_)`
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>* (_Low_) \<and> kind a' = (\<lambda>s. True)\<^sub>\<surd>"
  proof(induct as rule:rev_induct)
    case Nil
    with `inner_node n` show ?case by fastforce
  next
    case (snoc a' as')
    from `n -as'@[a']\<rightarrow>* (_Exit_)`
    have "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' = (_Exit_)"
      by(auto elim:path_split_snoc)
    { assume "sourcenode a' = (_Entry_)"
      with `n -as'\<rightarrow>* sourcenode a'` have "n = (_Entry_)"
        by(blast intro!:path_Entry_target)
      with `inner_node n` have False by(simp add:inner_node_def) }
    with `valid_edge a'` `targetnode a' = (_Exit_)` have "sourcenode a' = (_Low_)"
      by(blast dest!:Exit_edge_Entry_or_Low)
    from Low_source_Exit_edge
    obtain ax where "valid_edge ax" and "sourcenode ax = (_Low_)"
      and "targetnode ax = (_Exit_)" and "kind ax = (\<lambda>s. True)\<^sub>\<surd>"
      by blast
    with `valid_edge a'` `targetnode a' = (_Exit_)` `sourcenode a' = (_Low_)`
    have "a' = ax" by(fastforce intro:edge_det)
    with `n -as'\<rightarrow>* sourcenode a'` `sourcenode a' = (_Low_)` `kind ax = (\<lambda>s. True)\<^sub>\<surd>`
    show ?case by blast
  qed
qed


lemma not_Low_High: "V \<notin> L \<Longrightarrow> V \<in> H"
  using HighLowUNIV
  by fastforce

lemma not_High_Low: "V \<notin> H \<Longrightarrow> V \<in> L"
  using HighLowUNIV
  by fastforce


subsection {* Low Equivalence *}

text {*
In classical noninterference, an external observer can only see public values,
in our case the @{text L}-variables. If two states agree in the values of all 
@{text L}-variables, these states are indistinguishable for him. 
\emph{Low equivalence} groups those states in an equivalence class using 
the relation @{text "\<approx>\<^sub>L"}:
*}

definition lowEquivalence :: "('var \<rightharpoonup> 'val) list \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
(infixl "\<approx>\<^sub>L" 50)
  where "s \<approx>\<^sub>L s' \<equiv> \<forall>V \<in> L. hd s V = hd s' V"

text {* The following lemmas connect low equivalent states with
relevant variables as necessary in the correctness proof for slicing. *}

lemma relevant_vars_Entry:
  assumes "V \<in> rv S (CFG_node (_Entry_))" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "V \<in> L"
proof -
  from `V \<in> rv S (CFG_node (_Entry_))` obtain as n' 
    where "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
    and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
    and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
  from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'` have "valid_node (parent_node n')"
    by(fastforce intro:path_valid_node simp:intra_path_def)
  thus ?thesis
  proof(cases "parent_node n'" rule:valid_node_cases)
    case Entry
    with `V \<in> Use\<^bsub>SDG\<^esub> n'` have False
      by -(drule SDG_Use_parent_Use,simp add:Entry_empty)
    thus ?thesis by simp
  next
    case Exit
    with `V \<in> Use\<^bsub>SDG\<^esub> n'` have False
      by -(drule SDG_Use_parent_Use,simp add:Exit_empty)
    thus ?thesis by simp
  next
    case inner
    with `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'` obtain a' as' where "as = a'#as'"
      and "(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce elim:Entry_path_High_path simp:intra_path_def)
    from `(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'` `as = a'#as'`
    have "sourcenode a' = (_Entry_)" by(fastforce elim:path.cases simp:intra_path_def)
    show ?thesis
    proof(cases "as' = []")
      case True
      with `(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'` have "parent_node n' = (_High_)"
        by(fastforce simp:intra_path_def)
      with `n' \<in> HRB_slice S` `(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have False 
        by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice 
                    simp:SDG_to_CFG_set_def)
      thus ?thesis by simp
    next
      case False
      with `(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'` have "hd (sourcenodes as') = (_High_)"
        by(fastforce intro:path_sourcenode simp:intra_path_def)
      from False have "hd (sourcenodes as') \<in> set (sourcenodes as')"
        by(fastforce intro:hd_in_set simp:sourcenodes_def)
      with `as = a'#as'` have "hd (sourcenodes as') \<in> set (sourcenodes as)"
        by(simp add:sourcenodes_def)
      from `hd (sourcenodes as') = (_High_)`
      have "valid_node (hd (sourcenodes as'))" by simp
      have "valid_SDG_node (CFG_node (_High_))" by simp
      with `hd (sourcenodes as') = (_High_)`
        `hd (sourcenodes as') \<in> set (sourcenodes as)`
        `\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''`
      have "V \<notin> Def (_High_)"
        by(fastforce dest:CFG_Def_SDG_Def[OF `valid_node (hd (sourcenodes as'))`])
      hence "V \<notin> H" by(simp add:DefHigh)
      thus ?thesis by(rule not_High_Low)
    qed
  qed
qed



lemma lowEquivalence_relevant_nodes_Entry:
  assumes "s \<approx>\<^sub>L s'" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "\<forall>V \<in> rv S (CFG_node (_Entry_)). hd s V = hd s' V"
proof
  fix V assume "V \<in> rv S (CFG_node (_Entry_))"
  with `(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` have "V \<in> L" by -(rule relevant_vars_Entry)
  with `s \<approx>\<^sub>L s'` show "hd s V = hd s' V" by(simp add:lowEquivalence_def)
qed


subsection {* The Correctness Proofs *}

text {*
In the following, we present two correctness proofs that slicing
guarantees IFC noninterference. In both theorems, @{text "CFG_node
(_High_) \<notin> HRB_slice S"}, where @{text "CFG_node (_Low_) \<in> S"}, makes
sure that no high variable (which are all defined in @{text "(_High_)"})
can influence a low variable (which are all used in @{text "(_Low_)"}).


First, a theorem regarding @{text "(_Entry_) -as\<rightarrow>* (_Exit_)"} paths in the 
control flow graph (CFG), which agree to a complete program execution: *}


lemma slpa_rv_Low_Use_Low:
  assumes "CFG_node (_Low_) \<in> S"
  shows "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; same_level_path_aux cs as';
    \<forall>c \<in> set cs. valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
   \<forall>i < length cs. \<forall>V \<in> rv S (CFG_node (sourcenode (cs!i))). 
    fst (s!Suc i) V = fst (s'!Suc i) V; \<forall>i < Suc (length cs). snd (s!i) = snd (s'!i);
   \<forall>V \<in> rv S (CFG_node m). state_val s V = state_val s' V;
   preds (slice_kinds S as) s; preds (slice_kinds S as') s';
   length s = Suc (length cs); length s' = Suc (length cs)\<rbrakk>
   \<Longrightarrow> \<forall>V \<in> Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
                      state_val (transfers(slice_kinds S as') s') V"
proof(induct arbitrary:m as' s s' rule:slpa_induct)
  case (slpa_empty cs)
  from `m -[]\<rightarrow>* (_Low_)` have "m = (_Low_)" by fastforce
  from `m -[]\<rightarrow>* (_Low_)` have "valid_node m"
    by(rule path_valid_node)+
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from `valid_node m` `m = (_Low_)` have "(_Low_) -[]\<rightarrow>\<^sub>\<iota>* (_Low_)"
      by(fastforce intro:empty_path simp:intra_path_def)
    moreover
    from `valid_node m` `m = (_Low_)` `CFG_node (_Low_) \<in> S`
    have "CFG_node (_Low_) \<in> HRB_slice S"
      by(fastforce intro:HRB_slice_refl)
    ultimately have "V \<in> rv S (CFG_node m)" 
      using `m = (_Low_)`
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)" by simp
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    from `m -as'\<rightarrow>* (_Low_)` `m = (_Low_)` have "as' = []"
    proof(induct m as' m'\<equiv>"(_Low_)" rule:path.induct)
      case (Cons_path m'' as a m)
      from `valid_edge a` `sourcenode a = m` `m = (_Low_)`
      have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
      with `targetnode a = m''` `m'' -as\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?case by simp
    qed simp
    with `\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)`
      `\<forall>V \<in> rv S (CFG_node m). state_val s V = state_val s' V` Nil
    show ?thesis by(auto simp:slice_kinds_def)
  qed
next
  case (slpa_intra cs a as)
  note IH = `\<And>m as' s s'. \<lbrakk>upd_cs cs as = []; same_level_path_aux cs as'; 
    \<forall>a\<in>set cs. valid_edge a; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V; 
    \<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length cs); length s' = Suc (length cs)\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
    state_val (transfers(slice_kinds S as') s') V`
  note rvs = `\<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V`
  from `m -a # as\<rightarrow>* (_Low_)` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with `m -as'\<rightarrow>* (_Low_)` have "m = (_Low_)" by fastforce
      with `valid_edge a` `sourcenode a = m` have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from `valid_edge a` `sourcenode a = m` `m = (_Low_)` 
        `targetnode a = (_Exit_)` `valid_edge a'` `sourcenode a' = (_Low_)` 
        `targetnode a' = (_Exit_)`
      have "a = a'" by(fastforce dest:edge_det)
      with `kind a' = (\<lambda>s. True)\<^sub>\<surd>` have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with `targetnode a = (_Exit_)` `targetnode a -as\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with `m -as'\<rightarrow>* (_Low_)` have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from `preds (slice_kinds S (a # as)) s`
      obtain cf cfs where [simp]:"s = cf#cfs" by(cases s)(auto simp:slice_kinds_def)
      from `preds (slice_kinds S as') s'` `as' = ax # asx` 
      obtain cf' cfs' where [simp]:"s' = cf'#cfs'"
        by(cases s')(auto simp:slice_kinds_def)
      have "intra_kind (kind ax)"
      proof(cases "kind ax" rule:edge_kind_cases)
        case (Call Q r p fs)
        have False
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          with `intra_kind (kind a)` have "slice_kind S a = kind a"
            by -(rule slice_intra_kind_in_slice)
          from `valid_edge ax` `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          have unique:"\<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode ax \<and> 
            intra_kind(kind a')" by(rule call_only_one_intra_edge)
          from `valid_edge ax` `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain x 
            where "x \<in> get_return_edges ax" by(fastforce dest:get_return_edge_call)
          with `valid_edge ax` obtain a' where "valid_edge a'" 
            and "sourcenode a' = sourcenode ax" and "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
            by(fastforce dest:call_return_node_edge)
          with `valid_edge a` `sourcenode a = m` `sourcenode ax = m`
            `intra_kind (kind a)` unique
          have "a' = a" by(fastforce simp:intra_kind_def)
          with `kind a' = (\<lambda>cf. False)\<^sub>\<surd>` `slice_kind S a = kind a`
            `preds (slice_kinds S (a#as)) s`
          have False by(cases s)(auto simp:slice_kinds_def)
          thus ?thesis by simp
        next
          case False
          with `kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `sourcenode a = m` `sourcenode ax = m`
          have "slice_kind S ax = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            by(fastforce intro:slice_kind_Call)
          with `as' = ax # asx` `preds (slice_kinds S as') s'`
          have False by(cases s')(auto simp:slice_kinds_def)
          thus ?thesis by simp
        qed
        thus ?thesis by simp
      next
        case (Return Q p f)
        from `valid_edge ax` `kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `valid_edge a` `intra_kind (kind a)`
          `sourcenode a = m` `sourcenode ax = m`
        have False by -(drule return_edges_only,auto simp:intra_kind_def)
        thus ?thesis by simp
      qed simp
      with `same_level_path_aux cs as'` `as' = ax#asx`
      have "same_level_path_aux cs asx" by(fastforce simp:intra_kind_def)
      show ?thesis
      proof(cases "targetnode a = targetnode ax")
        case True
        with `valid_edge a` `valid_edge ax` `sourcenode a = m` `sourcenode ax = m`
        have "a = ax" by(fastforce intro:edge_det)
        with `valid_edge a` `intra_kind (kind a)` `sourcenode a = m`
          `\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V`
          `preds (slice_kinds S (a # as)) s`
          `preds (slice_kinds S as') s'` `as' = ax # asx`
        have rv:"\<forall>V\<in>rv S (CFG_node (targetnode a)). 
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V"
          by -(rule rv_edge_slice_kinds,auto)
        from `upd_cs cs (a # as) = []` `intra_kind (kind a)`
        have "upd_cs cs as = []" by(fastforce simp:intra_kind_def)
        from `targetnode ax -asx\<rightarrow>* (_Low_)` `a = ax`
        have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
        from `valid_edge a` `intra_kind (kind a)`
        obtain cfx 
          where cfx:"transfer (slice_kind S a) s = cfx#cfs \<and> snd cfx = snd cf"
          apply(cases cf)
          apply(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>") apply auto
          apply(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          apply(auto simp:intra_kind_def)
          apply(drule slice_kind_Upd) apply auto 
          by(erule kind_Predicate_notin_slice_slice_kind_Predicate) auto
        from `valid_edge a` `intra_kind (kind a)`
        obtain cfx' 
          where cfx':"transfer (slice_kind S a) s' = cfx'#cfs' \<and> snd cfx' = snd cf'"
          apply(cases cf')
          apply(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>") apply auto
          apply(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          apply(auto simp:intra_kind_def)
          apply(drule slice_kind_Upd) apply auto 
          by(erule kind_Predicate_notin_slice_slice_kind_Predicate) auto
        with cfx `\<forall>i < Suc (length cs). snd (s!i) = snd (s'!i)`
        have snds:"\<forall>i<Suc(length cs).
          snd (transfer (slice_kind S a) s ! i) = 
          snd (transfer (slice_kind S a) s' ! i)" 
          by auto(case_tac i,auto)
        from rvs cfx cfx' have rvs':"\<forall>i<length cs.
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
          fst (transfer (slice_kind S a) s ! Suc i) V =
          fst (transfer (slice_kind S a) s' ! Suc i) V"
          by fastforce
        from `preds (slice_kinds S (a # as)) s`
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)" by(simp add:slice_kinds_def)
        moreover
        from `preds (slice_kinds S as') s'` `as' = ax # asx` `a = ax`
        have "preds (slice_kinds S asx) (transfer (slice_kind S a) s')" 
          by(simp add:slice_kinds_def)
        moreover
        from `valid_edge a` `intra_kind (kind a)`
        have "length (transfer (slice_kind S a) s) = length s"
          by(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        (auto dest:slice_intra_kind_in_slice slice_kind_Upd
          elim:kind_Predicate_notin_slice_slice_kind_Predicate simp:intra_kind_def)
        with `length s = Suc (length cs)`
        have "length (transfer (slice_kind S a) s) = Suc (length cs)"
          by simp
        moreover
        from `a = ax` `valid_edge a` `intra_kind (kind a)`
        have "length (transfer (slice_kind S a) s') = length s'"
          by(cases "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        (auto dest:slice_intra_kind_in_slice slice_kind_Upd
          elim:kind_Predicate_notin_slice_slice_kind_Predicate simp:intra_kind_def)
        with `length s' = Suc (length cs)`
        have "length (transfer (slice_kind S a) s') = Suc (length cs)"
          by simp
        moreover
        from IH[OF `upd_cs cs as = []` `same_level_path_aux cs asx` 
          `\<forall>c\<in>set cs. valid_edge c` `targetnode a -as\<rightarrow>* (_Low_)` 
          `targetnode a -asx\<rightarrow>* (_Low_)` rvs' snds rv calculation]
          `as' = ax # asx` `a = ax`
        show ?thesis by(simp add:slice_kinds_def)
      next
        case False
        from `\<forall>i < Suc(length cs). snd (s!i) = snd (s'!i)`
        have "snd (hd s) = snd (hd s')" by(erule_tac x="0" in allE) fastforce
        with `valid_edge a` `valid_edge ax` `sourcenode a = m`
          `sourcenode ax = m` `as' = ax # asx` False
          `intra_kind (kind a)` `intra_kind (kind ax)`
          `preds (slice_kinds S (a # as)) s`
          `preds (slice_kinds S as') s'`
          `\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V`
          `length s = Suc (length cs)` `length s' = Suc (length cs)`
        have False by(fastforce intro!:rv_branching_edges_slice_kinds_False[of a ax])
        thus ?thesis by simp
      qed
    qed
  qed
next
  case (slpa_Call cs a as Q r p fs)
  note IH = `\<And>m as' s s'. 
    \<lbrakk>upd_cs (a # cs) as = []; same_level_path_aux (a # cs) as';
    \<forall>c\<in>set (a # cs). valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length (a # cs). \<forall>V\<in>rv S (CFG_node (sourcenode ((a # cs) ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V;
    \<forall>i<Suc (length (a # cs)). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length (a # cs)); length s' = Suc (length (a # cs))\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
    state_val (transfers(slice_kinds S as') s') V`
  note rvs = `\<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V`
  from `m -a # as\<rightarrow>* (_Low_)` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  from `\<forall>c\<in>set cs. valid_edge c` `valid_edge a`
  have "\<forall>c\<in>set (a # cs). valid_edge c" by simp
  show ?case
   proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with `m -as'\<rightarrow>* (_Low_)` have "m = (_Low_)" by fastforce
      with `valid_edge a` `sourcenode a = m` have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from `valid_edge a` `sourcenode a = m` `m = (_Low_)` 
        `targetnode a = (_Exit_)` `valid_edge a'` `sourcenode a' = (_Low_)` 
        `targetnode a' = (_Exit_)`
      have "a = a'" by(fastforce dest:edge_det)
      with `kind a' = (\<lambda>s. True)\<^sub>\<surd>` have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with `targetnode a = (_Exit_)` `targetnode a -as\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with `m -as'\<rightarrow>* (_Low_)` have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from `preds (slice_kinds S (a # as)) s`
      obtain cf cfs where [simp]:"s = cf#cfs" by(cases s)(auto simp:slice_kinds_def)
      from `preds (slice_kinds S as') s'` `as' = ax # asx` 
      obtain cf' cfs' where [simp]:"s' = cf'#cfs'"
        by(cases s')(auto simp:slice_kinds_def)
      have "\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      proof(cases "kind ax" rule:edge_kind_cases)
        case Intra
        have False
        proof(cases "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          with `intra_kind (kind ax)` 
          have "slice_kind S ax = kind ax"
            by -(rule slice_intra_kind_in_slice)
          from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          have unique:"\<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
            intra_kind(kind a')" by(rule call_only_one_intra_edge)
          from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain x 
            where "x \<in> get_return_edges a" by(fastforce dest:get_return_edge_call)
          with `valid_edge a` obtain a' where "valid_edge a'" 
            and "sourcenode a' = sourcenode a" and "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
            by(fastforce dest:call_return_node_edge)
          with `valid_edge ax` `sourcenode ax = m` `sourcenode a = m`
            `intra_kind (kind ax)` unique
          have "a' = ax" by(fastforce simp:intra_kind_def)
          with `kind a' = (\<lambda>cf. False)\<^sub>\<surd>` 
            `slice_kind S ax = kind ax` `as' = ax # asx`
            `preds (slice_kinds S as') s'`
          have False by(simp add:slice_kinds_def)
          thus ?thesis by simp
        next
          case False
          with `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `sourcenode ax = m` `sourcenode a = m`
          have "slice_kind S a = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            by(fastforce intro:slice_kind_Call)
          with `preds (slice_kinds S (a # as)) s`
          have False by(simp add:slice_kinds_def)
          thus ?thesis by simp
        qed
        thus ?thesis by simp
      next
        case (Return Q' p' f')
        from `valid_edge ax` `kind ax = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'` `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
          `sourcenode a = m` `sourcenode ax = m`
        have False by -(drule return_edges_only,auto)
        thus ?thesis by simp
      qed simp
      have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof(rule ccontr)
        assume "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        from this `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        have "slice_kind S a = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
          by(rule slice_kind_Call)
        with `preds (slice_kinds S (a # as)) s`
        show False by(simp add:slice_kinds_def)
      qed
      with `preds (slice_kinds S (a # as)) s` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "pred (kind a) s" 
        by(fastforce dest:slice_kind_Call_in_slice simp:slice_kinds_def)
      from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
        `sourcenode a = m` `sourcenode ax = m`
      have "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      with `as' = ax # asx` `preds (slice_kinds S as') s'` 
        `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "pred (kind ax) s'"
        by(fastforce dest:slice_kind_Call_in_slice simp:slice_kinds_def)
      { fix V assume "V \<in> Use (sourcenode a)"
        from `valid_edge a` have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
          by(fastforce intro:empty_path simp:intra_path_def)
        with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `valid_edge a` `V \<in> Use (sourcenode a)`
        have "V \<in> rv S (CFG_node (sourcenode a))"
          by(auto intro!:rvI CFG_Use_SDG_Use simp:SDG_to_CFG_set_def sourcenodes_def) }
      with `\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V`
        `sourcenode a = m`
      have Use:"\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by simp
      from `\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)`
      have "snd (hd s) = snd (hd s')"  by fastforce
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `valid_edge ax`
        `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `sourcenode a = m` `sourcenode ax = m`
        `pred (kind a) s` `pred (kind ax) s'` Use `length s = Suc (length cs)`
        `length s' = Suc (length cs)`
      have [simp]:"ax = a" by(fastforce intro!:CFG_equal_Use_equal_call)
      from `same_level_path_aux cs as'` `as' = ax#asx` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
        `\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "same_level_path_aux (a # cs) asx" by simp
      from `targetnode ax -asx\<rightarrow>* (_Low_)` have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
      from `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `upd_cs cs (a # as) = []` 
      have "upd_cs (a # cs) as = []" by simp
      from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have slice_kind:"slice_kind S a = 
        Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
        by(rule slice_kind_Call_in_slice)
      from `\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)` slice_kind
      have snds:"\<forall>i<Suc (length (a # cs)).
        snd (transfer (slice_kind S a) s ! i) =
        snd (transfer (slice_kind S a) s' ! i)"
        by auto(case_tac i,auto)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain ins outs 
        where "(p,ins,outs) \<in> set procs" by(fastforce dest!:callee_in_procs)
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
      have "length (ParamUses (sourcenode a)) = length ins"
        by(fastforce intro:ParamUses_call_source_length)
      with `valid_edge a`
      have "\<forall>i < length ins. \<forall>V \<in> (ParamUses (sourcenode a))!i. V \<in> Use (sourcenode a)"
        by(fastforce intro:ParamUses_in_Use)
      with `\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V`
      have "\<forall>i < length ins. \<forall>V \<in> (ParamUses (sourcenode a))!i. 
        state_val s V = state_val s' V"
        by fastforce
      with `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
        `pred (kind a) s` `pred (kind ax) s'`
      have "\<forall>i < length ins. (params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i"
        by(fastforce intro!:CFG_call_edge_params)
      from `valid_edge a` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` `(p,ins,outs) \<in> set procs`
      have "length fs = length ins" by(rule CFG_call_edge_length)
      { fix i assume "i < length fs"
        with `length fs = length ins` have "i < length ins" by simp
        from `i < length fs` have "(params fs (fst cf))!i = (fs!i) (fst cf)"
          by(rule params_nth)
        moreover
        from `i < length fs` have "(params fs (fst cf'))!i = (fs!i) (fst cf')"
          by(rule params_nth)
        ultimately have "(fs!i) (fst (hd s)) = (fs!i) (fst (hd s'))"
          using `i < length ins`
            `\<forall>i < length ins. (params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i`
          by simp }
      hence "\<forall>i < length fs. (fs ! i) (fst cf) = (fs ! i) (fst cf')" by simp
      { fix i assume "i < length fs"
        with `\<forall>i < length fs. (fs ! i) (fst cf) = (fs ! i) (fst cf')`
        have "(fs ! i) (fst cf) = (fs ! i) (fst cf')" by simp
        have "((csppa (targetnode a) (HRB_slice S) 0 fs)!i)(fst cf) =
          ((csppa (targetnode a) (HRB_slice S) 0 fs)!i)(fst cf')"
        proof(cases "Formal_in(targetnode a,i + 0) \<in>  HRB_slice S")
          case True
          with `i < length fs` 
          have "(csppa (targetnode a) (HRB_slice S) 0 fs)!i = fs!i"
            by(rule csppa_Formal_in_in_slice)
          with `(fs ! i) (fst cf) = (fs ! i) (fst cf')` show ?thesis by simp
        next
          case False
          with `i < length fs` 
          have "(csppa (targetnode a) (HRB_slice S) 0 fs)!i = empty"
            by(rule csppa_Formal_in_notin_slice)
          thus ?thesis by simp
        qed }
      hence eq:"\<forall>i < length fs.
        ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf) =
        ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf')"
        by(simp add:cspp_def)
      { fix i assume "i < length fs"
        hence "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf))!i =
          ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf)"
          by(fastforce intro:params_nth)
        moreover
        from `i < length fs`
        have "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf'))!i =
          ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf')"
          by(fastforce intro:params_nth)
        ultimately 
        have "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf))!i =
          (params (cspp (targetnode a) (HRB_slice S) fs)(fst cf'))!i"
          using eq `i < length fs` by simp }
      hence "params (cspp (targetnode a) (HRB_slice S) fs)(fst cf) =
        params (cspp (targetnode a) (HRB_slice S) fs)(fst cf')"
        by(simp add:list_eq_iff_nth_eq)
      with slice_kind `(p,ins,outs) \<in> set procs`
      obtain cfx where [simp]:
        "transfer (slice_kind S a) (cf#cfs) = cfx#cf#cfs"
        "transfer (slice_kind S a) (cf'#cfs') = cfx#cf'#cfs'"
        by auto
      hence rv:"\<forall>V\<in>rv S (CFG_node (targetnode a)).
        state_val (transfer (slice_kind S a) s) V = 
        state_val (transfer (slice_kind S a) s') V" by simp
      from rvs `\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V` 
        `sourcenode a = m`
      have rvs':"\<forall>i<length (a # cs). 
        \<forall>V\<in>rv S (CFG_node (sourcenode ((a # cs) ! i))).
        fst ((transfer (slice_kind S a) s) ! Suc i) V = 
        fst ((transfer (slice_kind S a) s') ! Suc i) V"
        by auto(case_tac i,auto)
      from `preds (slice_kinds S (a # as)) s`
      have "preds (slice_kinds S as)
        (transfer (slice_kind S a) s)" by(simp add:slice_kinds_def)
      moreover
      from `preds (slice_kinds S as') s'` `as' = ax#asx`
      have "preds (slice_kinds S asx)
        (transfer (slice_kind S a) s')" by(simp add:slice_kinds_def)
      moreover
      from `length s = Suc (length cs)`
      have "length (transfer (slice_kind S a) s) = 
        Suc (length (a # cs))" by simp
      moreover
      from `length s' = Suc (length cs)`
      have "length (transfer (slice_kind S a) s') = 
        Suc (length (a # cs))" by simp
      moreover
      from IH[OF `upd_cs (a # cs) as = []` `same_level_path_aux (a # cs) asx`
        `\<forall>c\<in>set (a # cs). valid_edge c` `targetnode a -as\<rightarrow>* (_Low_)`
        `targetnode a -asx\<rightarrow>* (_Low_)` rvs' snds rv calculation] `as' = ax#asx`
      show ?thesis by(simp add:slice_kinds_def)
    qed
  qed
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = `\<And>m as' s s'. \<lbrakk>upd_cs cs' as = []; same_level_path_aux cs' as'; 
    \<forall>c\<in>set cs'. valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length cs'. \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V; 
    \<forall>i<Suc (length cs'). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length cs'); length s' = Suc (length cs')\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
                       state_val (transfers(slice_kinds S as') s') V`
  note rvs = ` \<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V`
  from `m -a # as\<rightarrow>* (_Low_)` have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  from `\<forall>c\<in>set cs. valid_edge c` `cs = c' # cs'`
  have "valid_edge c'" and "\<forall>c\<in>set cs'. valid_edge c" by simp_all
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with `m -as'\<rightarrow>* (_Low_)` have "m = (_Low_)" by fastforce
      with `valid_edge a` `sourcenode a = m` have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from `valid_edge a` `sourcenode a = m` `m = (_Low_)` 
        `targetnode a = (_Exit_)` `valid_edge a'` `sourcenode a' = (_Low_)` 
        `targetnode a' = (_Exit_)`
      have "a = a'" by(fastforce dest:edge_det)
      with `kind a' = (\<lambda>s. True)\<^sub>\<surd>` have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with `targetnode a = (_Exit_)` `targetnode a -as\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with `m -as'\<rightarrow>* (_Low_)` have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from `valid_edge a` `valid_edge ax` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
        `sourcenode a = m` `sourcenode ax = m`
      have "\<exists>Q f. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by(auto dest:return_edges_only)
      with `same_level_path_aux cs as'` `as' = ax#asx` `cs = c' # cs'`
      have "ax \<in> get_return_edges c'" and "same_level_path_aux cs' asx" by auto
      from `valid_edge c'` `ax \<in> get_return_edges c'` `a \<in> get_return_edges c'`
      have [simp]:"ax = a" by(rule get_return_edges_unique)
      from `targetnode ax -asx\<rightarrow>* (_Low_)` have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
      from `upd_cs cs (a # as) = []` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `cs = c' # cs'`
        `a \<in> get_return_edges c'`
      have "upd_cs cs' as = []" by simp
      from `length s = Suc (length cs)` `cs = c' # cs'`
      obtain cf cfx cfs where "s = cf#cfx#cfs"
        by(cases s,auto,case_tac list,fastforce+)
      from `length s' = Suc (length cs)` `cs = c' # cs'`
      obtain cf' cfx' cfs' where "s' = cf'#cfx'#cfs'"
        by(cases s',auto,case_tac list,fastforce+)
      from rvs `cs = c' # cs'` `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
      have rvs1:"\<forall>i<length cs'. 
        \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
        fst ((cfx#cfs) ! Suc i) V = fst ((cfx'#cfs') ! Suc i) V"
        and "\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
        (fst cfx) V = (fst cfx') V"
        by auto
      from `valid_edge c'` `a \<in> get_return_edges c'`
      obtain Qx rx px fsx where "kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx"
        by(fastforce dest!:only_call_get_return_edges)
      have "\<forall>V \<in> rv S (CFG_node (targetnode a)).
        V \<in> rv S (CFG_node (sourcenode c'))"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a))"
        from `valid_edge c'` `a \<in> get_return_edges c'`
        obtain a' where edge:"valid_edge a'" "sourcenode a' = sourcenode c'"
          "targetnode a' = targetnode a" "intra_kind (kind a')"
          by -(drule call_return_node_edge,auto simp:intra_kind_def)
        from `V \<in> rv S (CFG_node (targetnode a))`
        obtain as n' where "targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and all:"\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
        from `targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'` edge
        have "sourcenode c' -a'#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from `valid_edge c'` `kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx` have "Def (sourcenode c') = {}"
          by(rule call_source_Def_empty)
        hence "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' = sourcenode c'
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce dest:SDG_Def_parent_Def)
        with all `sourcenode a' = sourcenode c'`
        have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a'#as)) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce simp:sourcenodes_def)
        with `sourcenode c' -a'#as\<rightarrow>\<^sub>\<iota>* parent_node n'` 
          `n' \<in> HRB_slice S` `V \<in> Use\<^bsub>SDG\<^esub> n'`
        show "V \<in> rv S (CFG_node (sourcenode c'))"
          by(fastforce intro:rvI)
      qed
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        from `valid_edge c'` `a \<in> get_return_edges c'`
        have "get_proc (targetnode c') = get_proc (sourcenode a)"
          by -(drule intra_proc_additional_edge,
            auto dest:get_proc_intra simp:intra_kind_def)
        moreover
        from `valid_edge c'` `kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx`
        have "get_proc (targetnode c') = px" by(rule get_proc_call)
        moreover
        from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
        have "get_proc (sourcenode a) = p" by(rule get_proc_return)
        ultimately have [simp]:"px = p" by simp
        from `valid_edge c'` `kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx`
        obtain ins outs where "(p,ins,outs) \<in> set procs"
          by(fastforce dest!:callee_in_procs)
        with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
        have slice_kind:"slice_kind S a = 
          Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
          by(rule slice_kind_Return_in_slice)
        with `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
        have sx:"transfer (slice_kind S a) s = 
          (rspp (targetnode a) (HRB_slice S) outs (fst cfx) (fst cf),
          snd cfx)#cfs"
          and sx':"transfer (slice_kind S a) s' = 
          (rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf'),
          snd cfx')#cfs'"
          by simp_all
        with rvs1 have rvs':"\<forall>i<length cs'. 
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
          fst ((transfer (slice_kind S a) s) ! Suc i) V = 
          fst ((transfer (slice_kind S a) s') ! Suc i) V"
          by fastforce
        from slice_kind `\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)` `cs = c' # cs'`
          `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
        have snds:"\<forall>i<Suc (length cs').
          snd (transfer (slice_kind S a) s ! i) =
          snd (transfer (slice_kind S a) s' ! i)"
          apply auto apply(case_tac i) apply auto
          by(erule_tac x="Suc (Suc nat)" in allE) auto
        have "\<forall>V\<in>rv S (CFG_node (targetnode a)).
          (rspp (targetnode a) (HRB_slice S) outs 
          (fst cfx) (fst cf)) V =
          (rspp (targetnode a) (HRB_slice S) outs 
          (fst cfx') (fst cf')) V"
        proof
          fix V assume "V \<in> rv S (CFG_node (targetnode a))"
          show "(rspp (targetnode a) (HRB_slice S) outs 
            (fst cfx) (fst cf)) V =
            (rspp (targetnode a) (HRB_slice S) outs 
            (fst cfx') (fst cf')) V"
          proof(cases "V \<in> set (ParamDefs (targetnode a))")
            case True
            then obtain i where "i < length (ParamDefs (targetnode a))"
              and "(ParamDefs (targetnode a))!i = V"
              by(fastforce simp:in_set_conv_nth)
            from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs`
            have "length(ParamDefs (targetnode a)) = length outs"
              by(fastforce intro:ParamDefs_return_target_length)
            show ?thesis
            proof(cases "Actual_out(targetnode a,i) \<in> HRB_slice S")
              case True
              with `i < length (ParamDefs (targetnode a))` `valid_edge a`
                `length(ParamDefs (targetnode a)) = length outs`
                `(ParamDefs (targetnode a))!i = V`[THEN sym]
              have rspp_eq:"(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx) (fst cf)) V = 
                (fst cf)(outs!i)"
                "(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx') (fst cf')) V = 
                (fst cf')(outs!i)"
                by(auto intro:rspp_Actual_out_in_slice)
              from `valid_edge a` `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f` `(p,ins,outs) \<in> set procs`
              have "\<forall>V \<in> set outs. V \<in> Use (sourcenode a)" by(fastforce dest:outs_in_Use)
              have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node m)"
              proof
                fix V assume "V \<in> Use (sourcenode a)"
                from `valid_edge a` `sourcenode a = m`
                have "parent_node (CFG_node m) -[]\<rightarrow>\<^sub>\<iota>* parent_node (CFG_node m)"
                  by(fastforce intro:empty_path simp:intra_path_def)
                with `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
                  `V \<in> Use (sourcenode a)` `sourcenode a = m` `valid_edge a`
                show "V \<in> rv S (CFG_node m)"
                  by -(rule rvI,
                    auto intro!:CFG_Use_SDG_Use simp:SDG_to_CFG_set_def sourcenodes_def)
              qed
              with `\<forall>V \<in> set outs. V \<in> Use (sourcenode a)`
              have "\<forall>V \<in> set outs. V \<in> rv S (CFG_node m)" by simp
              with `\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V`
                `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
              have "\<forall>V \<in> set outs. (fst cf) V = (fst cf') V" by simp
              with `i < length (ParamDefs (targetnode a))`
                `length(ParamDefs (targetnode a)) = length outs`
              have "(fst cf)(outs!i) = (fst cf')(outs!i)" by fastforce
              with rspp_eq show ?thesis by simp
            next
              case False
              with `i < length (ParamDefs (targetnode a))` `valid_edge a`
                `length(ParamDefs (targetnode a)) = length outs`
                `(ParamDefs (targetnode a))!i = V`[THEN sym]
              have rspp_eq:"(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx) (fst cf)) V = 
                (fst cfx)((ParamDefs (targetnode a))!i)"
                "(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx') (fst cf')) V = 
                (fst cfx')((ParamDefs (targetnode a))!i)"
                by(auto intro:rspp_Actual_out_notin_slice)
              from `\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
                (fst cfx) V = (fst cfx') V`
                `V \<in> rv S (CFG_node (targetnode a))`
                `\<forall>V \<in> rv S (CFG_node (targetnode a)).
                V \<in> rv S (CFG_node (sourcenode c'))`
                `(ParamDefs (targetnode a))!i = V`[THEN sym]
              have "(fst cfx) (ParamDefs (targetnode a) ! i) =
                (fst cfx') (ParamDefs (targetnode a) ! i)" by fastforce
              with rspp_eq show ?thesis by fastforce
            qed
          next
            case False
            with `\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
              (fst cfx) V = (fst cfx') V`
              `V \<in> rv S (CFG_node (targetnode a))`
              `\<forall>V \<in> rv S (CFG_node (targetnode a)).
              V \<in> rv S (CFG_node (sourcenode c'))`
            show ?thesis by(fastforce simp:rspp_def map_merge_def)
          qed
        qed
        with sx sx'
        have rv':"\<forall>V\<in>rv S (CFG_node (targetnode a)).
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V"
          by fastforce
        from `preds (slice_kinds S (a # as)) s`
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)"
          by(simp add:slice_kinds_def)
        moreover
        from `preds (slice_kinds S as') s'` `as' = ax#asx`
        have "preds (slice_kinds S asx) 
          (transfer (slice_kind S a) s')"
          by(simp add:slice_kinds_def)
        moreover
        from `length s = Suc (length cs)` `cs = c' # cs'` sx
        have "length (transfer (slice_kind S a) s) = Suc (length cs')"
          by(simp,simp add:`s = cf#cfx#cfs`)
        moreover
        from `length s' = Suc (length cs)` `cs = c' # cs'` sx'
        have "length (transfer (slice_kind S a) s') = Suc (length cs')"
          by(simp,simp add:`s' = cf'#cfx'#cfs'`)
        moreover
        from IH[OF `upd_cs cs' as = []` `same_level_path_aux cs' asx` 
          `\<forall>c\<in>set cs'. valid_edge c` `targetnode a -as\<rightarrow>* (_Low_)` 
          `targetnode a -asx\<rightarrow>* (_Low_)` rvs' snds rv' calculation] `as' = ax#asx`
        show ?thesis by(simp add:slice_kinds_def)
      next
        case False
        from this `kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f`
        have slice_kind:"slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
          by(rule slice_kind_Return)
        with `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
        have [simp]:"transfer (slice_kind S a) s = cfx#cfs"
          "transfer (slice_kind S a) s' = cfx'#cfs'" by simp_all
        from slice_kind `\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)` 
          `cs = c' # cs'` `s = cf#cfx#cfs` `s' = cf'#cfx'#cfs'`
        have snds:"\<forall>i<Suc (length cs').
          snd (transfer (slice_kind S a) s ! i) =
          snd (transfer (slice_kind S a) s' ! i)" by fastforce
        from rvs1 have rvs':"\<forall>i<length cs'. 
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
          fst ((transfer (slice_kind S a) s) ! Suc i) V = 
          fst ((transfer (slice_kind S a) s') ! Suc i) V"
          by fastforce
        from `\<forall>V \<in> rv S (CFG_node (targetnode a)).
          V \<in> rv S (CFG_node (sourcenode c'))`
          `\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
          (fst cfx) V = (fst cfx') V`
        have rv':"\<forall>V\<in>rv S (CFG_node (targetnode a)).
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V" by simp
        from `preds (slice_kinds S (a # as)) s`
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)"
          by(simp add:slice_kinds_def)
        moreover
        from `preds (slice_kinds S as') s'` `as' = ax#asx`
        have "preds (slice_kinds S asx) 
          (transfer (slice_kind S a) s')"
          by(simp add:slice_kinds_def)
        moreover
        from `length s = Suc (length cs)` `cs = c' # cs'`
        have "length (transfer (slice_kind S a) s) = Suc (length cs')"
          by(simp,simp add:`s = cf#cfx#cfs`)
        moreover
        from `length s' = Suc (length cs)` `cs = c' # cs'`
        have "length (transfer (slice_kind S a) s') = Suc (length cs')"
          by(simp,simp add:`s' = cf'#cfx'#cfs'`)
        moreover
        from IH[OF `upd_cs cs' as = []` `same_level_path_aux cs' asx` 
          `\<forall>c\<in>set cs'. valid_edge c` `targetnode a -as\<rightarrow>* (_Low_)` 
          `targetnode a -asx\<rightarrow>* (_Low_)` rvs' snds rv' calculation] `as' = ax#asx`
        show ?thesis by(simp add:slice_kinds_def)
      qed
    qed
  qed
qed


lemma rv_Low_Use_Low:
  assumes "m -as\<rightarrow>\<^sub>\<surd>* (_Low_)" and "m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)" and "get_proc m = Main"
  and "\<forall>V \<in> rv S (CFG_node m). cf V = cf' V"
  and "preds (slice_kinds S as) [(cf,undefined)]"
  and "preds (slice_kinds S as') [(cf',undefined)]"
  and "CFG_node (_Low_) \<in> S"
  shows "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S as) [(cf,undefined)]) V =
    state_val (transfers(slice_kinds S as') [(cf',undefined)]) V"
proof(cases as)
  case Nil
  with `m -as\<rightarrow>\<^sub>\<surd>* (_Low_)` have "valid_node m" and "m = (_Low_)" 
    by(auto intro:path_valid_node simp:vp_def)
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from `valid_node m` `m = (_Low_)` have "(_Low_) -[]\<rightarrow>\<^sub>\<iota>* (_Low_)"
      by(fastforce intro:empty_path simp:intra_path_def)
    moreover
    from `valid_node m` `m = (_Low_)` `CFG_node (_Low_) \<in> S`
    have "CFG_node (_Low_) \<in> HRB_slice S"
      by(fastforce intro:HRB_slice_refl)
    ultimately have "V \<in> rv S (CFG_node m)" using `m = (_Low_)`
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)" by simp
  show ?thesis
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    from `m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)` have "m -as'\<rightarrow>* (_Low_)" by(simp add:vp_def)
    from `m -as'\<rightarrow>* (_Low_)` `m = (_Low_)` have "as' = []"
    proof(induct m as' m'\<equiv>"(_Low_)" rule:path.induct)
      case (Cons_path m'' as a m)
      from `valid_edge a` `sourcenode a = m` `m = (_Low_)`
      have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
      with `targetnode a = m''` `m'' -as\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?case by simp
    qed simp
    with Nil `\<forall>V \<in> rv S (CFG_node m). cf V = cf' V`
      `\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)`
    show ?thesis by(fastforce simp:slice_kinds_def)
  qed
next
  case (Cons ax asx)
  with `m -as\<rightarrow>\<^sub>\<surd>* (_Low_)` have "sourcenode ax = m" and "valid_edge ax"
    and "targetnode ax -asx\<rightarrow>* (_Low_)"
    by(auto elim:path_split_Cons simp:vp_def)
  show ?thesis
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with `m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)` have "m = (_Low_)" by(fastforce simp:vp_def)
      with `valid_edge ax` `sourcenode ax = m` have "targetnode ax = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from `valid_edge ax` `sourcenode ax = m` `m = (_Low_)` 
        `targetnode ax = (_Exit_)` `valid_edge a'` `sourcenode a' = (_Low_)` 
        `targetnode a' = (_Exit_)`
      have "ax = a'" by(fastforce dest:edge_det)
      with `kind a' = (\<lambda>s. True)\<^sub>\<surd>` have "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with `targetnode ax = (_Exit_)` `targetnode ax -asx\<rightarrow>* (_Low_)`
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax' asx')
      from `m -as\<rightarrow>\<^sub>\<surd>* (_Low_)` have "valid_path_aux [] as" and "m -as\<rightarrow>* (_Low_)"
        by(simp_all add:vp_def valid_path_def)
      from this `as = ax#asx` `get_proc m = Main`
      have "same_level_path_aux [] as \<and> upd_cs [] as = []"
        by -(rule vpa_Main_slpa[of _ _ m "(_Low_)"],
        (fastforce intro!:get_proc_Low simp:valid_call_list_def)+)
      hence "same_level_path_aux [] as" and "upd_cs [] as = []" by simp_all
      from `m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)` have "valid_path_aux [] as'" and "m -as'\<rightarrow>* (_Low_)"
        by(simp_all add:vp_def valid_path_def)
      from this `as' = ax'#asx'` `get_proc m = Main`
      have "same_level_path_aux [] as' \<and> upd_cs [] as' = []"
        by -(rule vpa_Main_slpa[of _ _ m "(_Low_)"],
        (fastforce intro!:get_proc_Low simp:valid_call_list_def)+)
      hence "same_level_path_aux [] as'" by simp
      from `same_level_path_aux [] as` `upd_cs [] as = []`
        `same_level_path_aux [] as'` `m -as\<rightarrow>* (_Low_)` `m -as'\<rightarrow>* (_Low_)`
        `\<forall>V \<in> rv S (CFG_node m). cf V = cf' V` `CFG_node (_Low_) \<in> S`
        `preds (slice_kinds S as) [(cf,undefined)]`
        `preds (slice_kinds S as') [(cf',undefined)]`
      show ?thesis by -(erule slpa_rv_Low_Use_Low,auto)
    qed
  qed
qed



lemma nonInterference_path_to_Low:
  assumes "[cf] \<approx>\<^sub>L [cf']" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Low_)" and "preds (kinds as) [(cf,undefined)]"
  and "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Low_)" and "preds (kinds as') [(cf',undefined)]"
  shows "map fst (transfers (kinds as) [(cf,undefined)]) \<approx>\<^sub>L 
         map fst (transfers (kinds as') [(cf',undefined)])"
proof -
  from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Low_)` `preds (kinds as) [(cf,undefined)]`
    `CFG_node (_Low_) \<in> S`
  obtain asx where "preds (slice_kinds S asx) [(cf,undefined)]"
    and "\<forall>V \<in> Use (_Low_). 
    state_val (transfers (slice_kinds S asx) [(cf,undefined)]) V = 
    state_val (transfers (kinds as) [(cf,undefined)]) V"
    and "slice_edges S [] as = slice_edges S [] asx"
    and "transfers (kinds as) [(cf,undefined)] \<noteq> []"
    and "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* (_Low_)" 
    by(erule fundamental_property_of_static_slicing)
  from `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Low_)` `preds (kinds as') [(cf',undefined)]`
    `CFG_node (_Low_) \<in> S`
  obtain asx' where "preds (slice_kinds S asx') [(cf',undefined)]"
    and "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V = 
    state_val (transfers(kinds as') [(cf',undefined)]) V"
    and "slice_edges S [] as' = 
    slice_edges S [] asx'"
    and "transfers (kinds as') [(cf',undefined)] \<noteq> []"
    and "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(erule fundamental_property_of_static_slicing)
  from `[cf] \<approx>\<^sub>L [cf']` `(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  have "\<forall>V \<in> rv S (CFG_node (_Entry_)). cf V = cf' V" 
    by(fastforce dest:lowEquivalence_relevant_nodes_Entry)
  with `(_Entry_) -asx \<rightarrow>\<^sub>\<surd>*(_Low_)` `(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* (_Low_)`
    `CFG_node (_Low_) \<in> S` `preds (slice_kinds S asx) [(cf,undefined)]`
    `preds (slice_kinds S asx') [(cf',undefined)]`
  have "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx) [(cf,undefined)]) V =
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V"
    by -(rule rv_Low_Use_Low,auto intro:get_proc_Entry)
  with `\<forall>V \<in> Use (_Low_). 
    state_val (transfers (slice_kinds S asx) [(cf,undefined)]) V = 
    state_val (transfers (kinds as) [(cf,undefined)]) V`
    `\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V = 
    state_val (transfers(kinds as') [(cf',undefined)]) V`
    `transfers (kinds as) [(cf,undefined)] \<noteq> []` 
    `transfers (kinds as') [(cf',undefined)] \<noteq> []`
  show ?thesis by(fastforce simp:lowEquivalence_def UseLow neq_Nil_conv)
qed


theorem nonInterference_path:
  assumes "[cf] \<approx>\<^sub>L [cf']" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" and "preds (kinds as) [(cf,undefined)]"
  and "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)" and "preds (kinds as') [(cf',undefined)]"
  shows "map fst (transfers (kinds as) [(cf,undefined)]) \<approx>\<^sub>L 
  map fst (transfers (kinds as') [(cf',undefined)])"
proof -
  from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` obtain x xs where "as = x#xs"
    and "(_Entry_) = sourcenode x" and "valid_edge x" 
    and "targetnode x -xs\<rightarrow>* (_Exit_)"
    apply(cases "as = []")
     apply(clarsimp simp:vp_def,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(fastforce elim:path_split_Cons simp:vp_def)
  from `(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)` have "valid_path as" by(simp add:vp_def)
  from `valid_edge x` have "valid_node (targetnode x)" by simp
  hence "inner_node (targetnode x)"
  proof(cases rule:valid_node_cases)
    case Entry
    with `valid_edge x` have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with `targetnode x -xs\<rightarrow>* (_Exit_)` have "xs = []"
      by -(drule path_Exit_source,auto)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from `valid_edge x` `valid_edge z` `(_Entry_) = sourcenode x` 
      `sourcenode z = (_Entry_)` Exit `targetnode z = (_Exit_)`
    have "x = z" by(fastforce intro:edge_det)
    with `preds (kinds as) [(cf,undefined)]` `as = x#xs` `xs = []`
      `kind z = (\<lambda>s. False)\<^sub>\<surd>` 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with `targetnode x -xs\<rightarrow>* (_Exit_)` obtain x' xs' where "xs = xs'@[x']"
    and "targetnode x -xs'\<rightarrow>* (_Low_)" and "kind x' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with `(_Entry_) = sourcenode x` `valid_edge x`
  have "(_Entry_) -x#xs'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from `valid_path as` `as = x#xs` `xs = xs'@[x']`
  have "valid_path (x#xs')"
    by(simp add:valid_path_def del:valid_path_aux.simps)
      (rule valid_path_aux_split,simp)
  with `(_Entry_) -x#xs'\<rightarrow>* (_Low_)` have "(_Entry_) -x#xs'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def)
  from `as = x#xs` `xs = xs'@[x']` have "as = (x#xs')@[x']" by simp
  with `preds (kinds as) [(cf,undefined)]` 
  have "preds (kinds (x#xs')) [(cf,undefined)]"
    by(simp add:kinds_def preds_split)
  from `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)` obtain y ys where "as' = y#ys"
    and "(_Entry_) = sourcenode y" and "valid_edge y" 
    and "targetnode y -ys\<rightarrow>* (_Exit_)"
    apply(cases "as' = []")
     apply(clarsimp simp:vp_def,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(fastforce elim:path_split_Cons simp:vp_def)
  from `(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)` have "valid_path as'" by(simp add:vp_def)
  from `valid_edge y` have "valid_node (targetnode y)" by simp
  hence "inner_node (targetnode y)"
  proof(cases rule:valid_node_cases)
    case Entry
    with `valid_edge y` have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with `targetnode y -ys\<rightarrow>* (_Exit_)` have "ys = []"
      by -(drule path_Exit_source,auto)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from `valid_edge y` `valid_edge z` `(_Entry_) = sourcenode y` 
      `sourcenode z = (_Entry_)` Exit `targetnode z = (_Exit_)`
    have "y = z" by(fastforce intro:edge_det)
    with `preds (kinds as') [(cf',undefined)]` `as' = y#ys` `ys = []`
      `kind z = (\<lambda>s. False)\<^sub>\<surd>` 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with `targetnode y -ys\<rightarrow>* (_Exit_)` obtain y' ys' where "ys = ys'@[y']"
    and "targetnode y -ys'\<rightarrow>* (_Low_)" and "kind y' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with `(_Entry_) = sourcenode y` `valid_edge y`
  have "(_Entry_) -y#ys'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from `valid_path as'` `as' = y#ys` `ys = ys'@[y']`
  have "valid_path (y#ys')"
    by(simp add:valid_path_def del:valid_path_aux.simps)
      (rule valid_path_aux_split,simp)
  with `(_Entry_) -y#ys'\<rightarrow>* (_Low_)` have "(_Entry_) -y#ys'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def)
  from `as' = y#ys` `ys = ys'@[y']` have "as' = (y#ys')@[y']" by simp
  with `preds (kinds as') [(cf',undefined)]` 
  have "preds (kinds (y#ys')) [(cf',undefined)]"
    by(simp add:kinds_def preds_split)
  from `[cf] \<approx>\<^sub>L [cf']` `(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `CFG_node (_Low_) \<in> S`
    `(_Entry_) -x#xs'\<rightarrow>\<^sub>\<surd>* (_Low_)` `preds (kinds (x#xs')) [(cf,undefined)]`
    `(_Entry_) -y#ys'\<rightarrow>\<^sub>\<surd>* (_Low_)` `preds (kinds (y#ys')) [(cf',undefined)]`
  have "map fst (transfers (kinds (x#xs')) [(cf,undefined)]) \<approx>\<^sub>L 
    map fst (transfers (kinds (y#ys')) [(cf',undefined)])"
    by(rule nonInterference_path_to_Low)
  with `as = x#xs` `xs = xs'@[x']` `kind x' = (\<lambda>s. True)\<^sub>\<surd>`
    `as' = y#ys` `ys = ys'@[y']` `kind y' = (\<lambda>s. True)\<^sub>\<surd>`
  show ?thesis
    apply(cases "transfers (map kind xs') (transfer (kind x) [(cf,undefined)])")
    apply (auto simp add:kinds_def transfers_split)
    by((cases "transfers (map kind ys') (transfer (kind y) [(cf',undefined)])"),
       (auto simp add:kinds_def transfers_split))+
qed


end

text {* The second theorem assumes that we have a operational semantics,
whose evaluations are written @{text "\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"} and which conforms 
to the CFG. The correctness theorem then states that if no high variable
influenced a low variable and the initial states were low equivalent, the
reulting states are again low equivalent: *}


locale NonInterferenceInter = 
  NonInterferenceInterGraph sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses 
    H L High Low +
  SemanticsProperty sourcenode targetnode kind valid_edge Entry get_proc
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list"
  and sem :: "'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> 'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51,0] 80)
  and H :: "'var set" and L :: "'var set" 
  and High :: "'node"  ("'('_High'_')") and Low :: "'node" ("'('_Low'_')") +
  fixes final :: "'com \<Rightarrow> bool"
  assumes final_edge_Low: "\<lbrakk>final c; n \<triangleq> c\<rbrakk> 
    \<Longrightarrow> \<exists>a. valid_edge a \<and> sourcenode a = n \<and> targetnode a = (_Low_) \<and> kind a = \<Up>id"
begin


text{* The following theorem needs the explicit edge from @{text "(_High_)"}
  to @{text n}. An approach using a @{text "init"} predicate for initial statements,
  being reachable from @{text "(_High_)"} via a @{text "(\<lambda>s. True)\<^sub>\<surd>"} edge,
  does not work as the same statement could be identified by several nodes, some
  initial, some not. E.g., in the program \texttt{while (True) Skip;;Skip}
  two nodes identify this inital statement: the initial node and the node
  within the loop (because of loop unrolling).*}

theorem nonInterference:
  assumes "[cf\<^sub>1] \<approx>\<^sub>L [cf\<^sub>2]" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "valid_edge a" and "sourcenode a = (_High_)" and "targetnode a = n" 
  and "kind a = (\<lambda>s. True)\<^sub>\<surd>" and "n \<triangleq> c" and "final c'"
  and "\<langle>c,[cf\<^sub>1]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1\<rangle>" and "\<langle>c,[cf\<^sub>2]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2\<rangle>"
  shows "s\<^sub>1 \<approx>\<^sub>L s\<^sub>2"
proof -
  from High_target_Entry_edge obtain ax where "valid_edge ax"
    and "sourcenode ax = (_Entry_)" and "targetnode ax = (_High_)"
    and "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by blast
  from `n \<triangleq> c` `\<langle>c,[cf\<^sub>1]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1\<rangle>`
  obtain n\<^sub>1 as\<^sub>1 cfs\<^sub>1 where "n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1" and "n\<^sub>1 \<triangleq> c'"
    and "preds (kinds as\<^sub>1) [(cf\<^sub>1,undefined)]" 
    and "transfers (kinds as\<^sub>1) [(cf\<^sub>1,undefined)] = cfs\<^sub>1" and "map fst cfs\<^sub>1 = s\<^sub>1"
    by(fastforce dest:fundamental_property)
  from `n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1` `valid_edge a` `sourcenode a = (_High_)` `targetnode a = n`
    `kind a = (\<lambda>s. True)\<^sub>\<surd>`
  have "(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1" by(fastforce intro:Cons_path simp:vp_def valid_path_def)
  from `final c'` `n\<^sub>1 \<triangleq> c'`
  obtain a\<^sub>1 where "valid_edge a\<^sub>1" and "sourcenode a\<^sub>1 = n\<^sub>1" 
    and "targetnode a\<^sub>1 = (_Low_)" and "kind a\<^sub>1 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>1 -[a\<^sub>1]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with `(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1` have "(_High_) -(a#as\<^sub>1)@[a\<^sub>1]\<rightarrow>* (_Low_)"
    by(fastforce intro!:path_Append simp:vp_def)
  with `valid_edge ax` `sourcenode ax = (_Entry_)` `targetnode ax = (_High_)`
  have "(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  moreover
  from `(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1` have "valid_path_aux [] (a#as\<^sub>1)"
    by(simp add:vp_def valid_path_def)
  with `kind a\<^sub>1 = \<Up>id` have "valid_path_aux [] ((a#as\<^sub>1)@[a\<^sub>1])"
    by(fastforce intro:valid_path_aux_Append)
  with `kind ax = (\<lambda>s. True)\<^sub>\<surd>` have "valid_path_aux [] (ax#((a#as\<^sub>1)@[a\<^sub>1]))"
    by simp
  ultimately have "(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def valid_path_def)
  from `valid_edge a` `kind a = (\<lambda>s. True)\<^sub>\<surd>` `sourcenode a = (_High_)`
    `targetnode a = n`
  have "get_proc n = get_proc (_High_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_High have "get_proc n = Main" by simp
  from `valid_edge a\<^sub>1` `sourcenode a\<^sub>1 = n\<^sub>1` `targetnode a\<^sub>1 = (_Low_)` `kind a\<^sub>1 = \<Up>id`
  have "get_proc n\<^sub>1 = get_proc (_Low_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_Low have "get_proc n\<^sub>1 = Main" by simp
  from `n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1` have "n -as\<^sub>1\<rightarrow>\<^bsub>sl\<^esub>* n\<^sub>1"
    by(cases as\<^sub>1)
      (auto dest!:vpa_Main_slpa intro:`get_proc n\<^sub>1 = Main` `get_proc n = Main`
             simp:vp_def valid_path_def valid_call_list_def slp_def 
                  same_level_path_def simp del:valid_path_aux.simps)
  then obtain cfx r where cfx:"transfers (map kind as\<^sub>1) [(cf\<^sub>1,undefined)] = [(cfx,r)]"
    by(fastforce elim:slp_callstack_length_equal simp:kinds_def)
  from `kind ax = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (\<lambda>s. True)\<^sub>\<surd>` 
    `preds (kinds as\<^sub>1) [(cf\<^sub>1,undefined)]` `kind a\<^sub>1 = \<Up>id` cfx 
  have "preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]"
    by(auto simp:kinds_def preds_split)
  from `n \<triangleq> c` `\<langle>c,[cf\<^sub>2]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2\<rangle>`
  obtain n\<^sub>2 as\<^sub>2 cfs\<^sub>2 where "n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2" and "n\<^sub>2 \<triangleq> c'"
    and "preds (kinds as\<^sub>2) [(cf\<^sub>2,undefined)]" 
    and "transfers (kinds as\<^sub>2) [(cf\<^sub>2,undefined)] = cfs\<^sub>2" and "map fst cfs\<^sub>2 = s\<^sub>2"
    by(fastforce dest:fundamental_property)
  from `n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2` `valid_edge a` `sourcenode a = (_High_)` `targetnode a = n`
    `kind a = (\<lambda>s. True)\<^sub>\<surd>`
  have "(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2" by(fastforce intro:Cons_path simp:vp_def valid_path_def)
  from `final c'` `n\<^sub>2 \<triangleq> c'`
  obtain a\<^sub>2 where "valid_edge a\<^sub>2" and "sourcenode a\<^sub>2 = n\<^sub>2" 
    and "targetnode a\<^sub>2 = (_Low_)" and "kind a\<^sub>2 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>2 -[a\<^sub>2]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with `(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2` have "(_High_) -(a#as\<^sub>2)@[a\<^sub>2]\<rightarrow>* (_Low_)"
    by(fastforce intro!:path_Append simp:vp_def)
  with `valid_edge ax` `sourcenode ax = (_Entry_)` `targetnode ax = (_High_)`
  have "(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  moreover
  from `(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2` have "valid_path_aux [] (a#as\<^sub>2)"
    by(simp add:vp_def valid_path_def)
  with `kind a\<^sub>2 = \<Up>id` have "valid_path_aux [] ((a#as\<^sub>2)@[a\<^sub>2])"
    by(fastforce intro:valid_path_aux_Append)
  with `kind ax = (\<lambda>s. True)\<^sub>\<surd>` have "valid_path_aux [] (ax#((a#as\<^sub>2)@[a\<^sub>2]))"
    by simp
  ultimately have "(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def valid_path_def)
  from `valid_edge a` `kind a = (\<lambda>s. True)\<^sub>\<surd>` `sourcenode a = (_High_)`
    `targetnode a = n`
  have "get_proc n = get_proc (_High_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_High have "get_proc n = Main" by simp
  from `valid_edge a\<^sub>2` `sourcenode a\<^sub>2 = n\<^sub>2` `targetnode a\<^sub>2 = (_Low_)` `kind a\<^sub>2 = \<Up>id`
  have "get_proc n\<^sub>2 = get_proc (_Low_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_Low have "get_proc n\<^sub>2 = Main" by simp
  from `n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2` have "n -as\<^sub>2\<rightarrow>\<^bsub>sl\<^esub>* n\<^sub>2"
    by(cases as\<^sub>2)
      (auto dest!:vpa_Main_slpa intro:`get_proc n\<^sub>2 = Main` `get_proc n = Main`
             simp:vp_def valid_path_def valid_call_list_def slp_def 
                  same_level_path_def simp del:valid_path_aux.simps)
  then obtain cfx' r' 
    where cfx':"transfers (map kind as\<^sub>2) [(cf\<^sub>2,undefined)] = [(cfx',r')]"
    by(fastforce elim:slp_callstack_length_equal simp:kinds_def)
  from `kind ax = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (\<lambda>s. True)\<^sub>\<surd>` 
    `preds (kinds as\<^sub>2) [(cf\<^sub>2,undefined)]` `kind a\<^sub>2 = \<Up>id` cfx' 
  have "preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)]"
    by(auto simp:kinds_def preds_split)
  from `[cf\<^sub>1] \<approx>\<^sub>L [cf\<^sub>2]` `(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `CFG_node (_Low_) \<in> S`
    `(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>\<^sub>\<surd>* (_Low_)` 
    `preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]`
    `(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>\<^sub>\<surd>* (_Low_)` 
    `preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)]`
  have "map fst (transfers (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]) \<approx>\<^sub>L 
        map fst (transfers (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)])"
    by(rule nonInterference_path_to_Low)
  with `kind ax = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (\<lambda>s. True)\<^sub>\<surd>` `kind a\<^sub>1 = \<Up>id` `kind a\<^sub>2 = \<Up>id`
    `transfers (kinds as\<^sub>1) [(cf\<^sub>1,undefined)] = cfs\<^sub>1` `map fst cfs\<^sub>1 = s\<^sub>1`
    `transfers (kinds as\<^sub>2) [(cf\<^sub>2,undefined)] = cfs\<^sub>2` `map fst cfs\<^sub>2 = s\<^sub>2`
  show ?thesis by(cases s\<^sub>1)(cases s\<^sub>2,(fastforce simp:kinds_def transfers_split)+)+
qed


end

end

