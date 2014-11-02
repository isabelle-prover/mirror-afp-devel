section {* Static backward slice *}

theory Slice imports SCDObservable Distance begin

context SDG begin

subsection {* Preliminary definitions on the parameter nodes for defining
  sliced call and return edges *}

fun csppa :: "'node \<Rightarrow> 'node SDG_node set \<Rightarrow> nat \<Rightarrow> 
  ((('var \<rightharpoonup> 'val) \<Rightarrow> 'val option) list) \<Rightarrow> ((('var \<rightharpoonup> 'val) \<Rightarrow> 'val option) list)"
  where "csppa m S x [] = []"
  | "csppa m S x (f#fs) = 
     (if Formal_in(m,x) \<notin> S then empty else f)#csppa m S (Suc x) fs"

definition cspp :: "'node \<Rightarrow> 'node SDG_node set \<Rightarrow> 
  ((('var \<rightharpoonup> 'val) \<Rightarrow> 'val option) list) \<Rightarrow> ((('var \<rightharpoonup> 'val) \<Rightarrow> 'val option) list)"
  where "cspp m S fs \<equiv> csppa m S 0 fs"

lemma [simp]: "length (csppa m S x fs) = length fs"
by(induct fs arbitrary:x)(auto)

lemma [simp]: "length (cspp m S fs) = length fs"
by(simp add:cspp_def)

lemma csppa_Formal_in_notin_slice: 
  "\<lbrakk>x < length fs; Formal_in(m,x + i) \<notin> S\<rbrakk>
  \<Longrightarrow> (csppa m S i fs)!x = empty"
by(induct fs arbitrary:i x,auto simp:nth_Cons')

lemma csppa_Formal_in_in_slice: 
  "\<lbrakk>x < length fs; Formal_in(m,x + i) \<in> S\<rbrakk>
  \<Longrightarrow> (csppa m S i fs)!x = fs!x"
by(induct fs arbitrary:i x,auto simp:nth_Cons')


definition map_merge :: "('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 
                         'var list \<Rightarrow> ('var \<rightharpoonup> 'val)"
where "map_merge f g Q xs \<equiv> (\<lambda>V. if (\<exists>i. i < length xs \<and> xs!i = V \<and> Q i) then g V 
                                 else f V)"


definition rspp :: "'node \<Rightarrow> 'node SDG_node set \<Rightarrow> 'var list \<Rightarrow> 
  ('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val)"
where "rspp m S xs f g \<equiv> map_merge f (empty(ParamDefs m [:=] map g xs))
  (\<lambda>i. Actual_out(m,i) \<in> S) (ParamDefs m)"


lemma rspp_Actual_out_in_slice:
  assumes "x < length (ParamDefs (targetnode a))" and "valid_edge a"
  and "length (ParamDefs (targetnode a)) = length xs" 
  and "Actual_out (targetnode a,x) \<in> S"
  shows "(rspp (targetnode a) S xs f g) ((ParamDefs (targetnode a))!x) = g(xs!x)"
proof -
  from `valid_edge a` have "distinct(ParamDefs (targetnode a))"
    by(rule distinct_ParamDefs)
  from `x < length (ParamDefs (targetnode a))` 
    `length (ParamDefs (targetnode a)) = length xs`
    `distinct(ParamDefs (targetnode a))`
  have "(empty(ParamDefs (targetnode a) [:=] map g xs))
    ((ParamDefs (targetnode a))!x) = (map g xs)!x"
    by(fastforce intro:fun_upds_nth)
  with `Actual_out(targetnode a,x) \<in> S` `x < length (ParamDefs (targetnode a))`
    `length (ParamDefs (targetnode a)) = length xs` show ?thesis
    by(fastforce simp:rspp_def map_merge_def)
qed

lemma rspp_Actual_out_notin_slice:
  assumes "x < length (ParamDefs (targetnode a))" and "valid_edge a"
  and "length (ParamDefs (targetnode a)) = length xs" 
  and "Actual_out((targetnode a),x) \<notin> S"
  shows "(rspp (targetnode a) S xs f g) ((ParamDefs (targetnode a))!x) = 
  f((ParamDefs (targetnode a))!x)"
proof -
  from `valid_edge a` have "distinct(ParamDefs (targetnode a))"
    by(rule distinct_ParamDefs)
  from `x < length (ParamDefs (targetnode a))` 
    `length (ParamDefs (targetnode a)) = length xs`
    `distinct(ParamDefs (targetnode a))`
  have "(empty(ParamDefs (targetnode a) [:=] map g xs))
    ((ParamDefs (targetnode a))!x) = (map g xs)!x"
    by(fastforce intro:fun_upds_nth)
  with `Actual_out((targetnode a),x) \<notin> S` `distinct(ParamDefs (targetnode a))` 
    `x < length (ParamDefs (targetnode a))`
  show ?thesis by(fastforce simp:rspp_def map_merge_def nth_eq_iff_index_eq)
qed


subsection {* Defining the sliced edge kinds *}

primrec slice_kind_aux :: "'node \<Rightarrow> 'node \<Rightarrow> 'node SDG_node set \<Rightarrow> 
  ('var,'val,'ret,'pname) edge_kind \<Rightarrow> ('var,'val,'ret,'pname) edge_kind"
where "slice_kind_aux m m' S \<Up>f = (if m \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> then \<Up>f else \<Up>id)"
  | "slice_kind_aux m m' S (Q)\<^sub>\<surd> = (if m \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> then (Q)\<^sub>\<surd> else
  (if obs_intra m \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> = {} then 
    (let mex = (THE mex. method_exit mex \<and> get_proc m = get_proc mex) in
    (if (\<exists>x. distance m' mex x \<and> distance m mex (x + 1) \<and>
        (m' = (SOME mx'. \<exists>a'. m = sourcenode a' \<and> 
                              distance (targetnode a') mex x \<and>
                              valid_edge a' \<and> intra_kind(kind a') \<and>
                              targetnode a' = mx'))) 
          then (\<lambda>cf. True)\<^sub>\<surd> else (\<lambda>cf. False)\<^sub>\<surd>))
     else (let mx = THE mx. mx \<in> obs_intra m \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> in 
       (if (\<exists>x. distance m' mx x \<and> distance m mx (x + 1) \<and>
            (m' = (SOME mx'. \<exists>a'. m = sourcenode a' \<and> 
                                  distance (targetnode a') mx x \<and>
                                  valid_edge a' \<and> intra_kind(kind a') \<and>
                                  targetnode a' = mx'))) 
          then (\<lambda>cf. True)\<^sub>\<surd> else (\<lambda>cf. False)\<^sub>\<surd>))))"
  | "slice_kind_aux m m' S (Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) = (if m \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> then (Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp m' S fs))
                           else ((\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs))"
  | "slice_kind_aux m m' S (Q\<hookleftarrow>\<^bsub>p\<^esub>f) = (if m \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> then 
      (let outs = THE outs. \<exists>ins. (p,ins,outs) \<in> set procs in
         (Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp m' S outs cf' cf)))
    else ((\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')))"

definition slice_kind :: "'node SDG_node set \<Rightarrow> 'edge \<Rightarrow> 
  ('var,'val,'ret,'pname) edge_kind"
  where "slice_kind S a \<equiv> 
  slice_kind_aux (sourcenode a) (targetnode a) (HRB_slice S) (kind a)"

definition slice_kinds :: "'node SDG_node set \<Rightarrow> 'edge list \<Rightarrow> 
  ('var,'val,'ret,'pname) edge_kind list"
  where "slice_kinds S as \<equiv> map (slice_kind S) as"



lemma slice_intra_kind_in_slice:
  "\<lbrakk>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; intra_kind (kind a)\<rbrakk> 
  \<Longrightarrow> slice_kind S a = kind a"
by(fastforce simp:intra_kind_def slice_kind_def)


lemma slice_kind_Upd:
  "\<lbrakk>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; kind a = \<Up>f\<rbrakk> \<Longrightarrow> slice_kind S a = \<Up>id"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_empty_obs_nearer_SOME:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>"
  and "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" 
  and "method_exit mex" and "get_proc (sourcenode a) = get_proc mex"
  and "distance (targetnode a) mex x" and "distance (sourcenode a) mex (x + 1)"
  and "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') mex x \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = n')"
  shows "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
proof -
  from `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
  have "mex = (THE mex. method_exit mex \<and> get_proc (sourcenode a) = get_proc mex)"
    by(auto intro!:the_equality[THEN sym] intro:method_exit_unique)
  with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>` 
    `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
  have "slice_kind S a = 
    (if (\<exists>x. distance (targetnode a) mex x \<and> distance (sourcenode a) mex (x + 1) \<and>
    (targetnode a = (SOME mx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
    distance (targetnode a') mex x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
    targetnode a' = mx'))) then (\<lambda>cf. True)\<^sub>\<surd> else (\<lambda>cf. False)\<^sub>\<surd>)"
    by(simp add:slice_kind_def Let_def)
  with `distance (targetnode a) mex x` `distance (sourcenode a) mex (x + 1)`
    `targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') mex x \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = n')`
  show ?thesis by fastforce
qed


lemma slice_kind_Pred_empty_obs_nearer_not_SOME:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>"
  and "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" 
  and "method_exit mex" and "get_proc (sourcenode a) = get_proc mex"
  and "distance (targetnode a) mex x" and "distance (sourcenode a) mex (x + 1)"
  and "targetnode a \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') mex x \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = n')"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
  have "mex = (THE mex. method_exit mex \<and> get_proc (sourcenode a) = get_proc mex)"
    by(auto intro!:the_equality[THEN sym] intro:method_exit_unique)
  with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>` 
    `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
  have "slice_kind S a = 
    (if (\<exists>x. distance (targetnode a) mex x \<and> distance (sourcenode a) mex (x + 1) \<and>
    (targetnode a = (SOME mx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
    distance (targetnode a') mex x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
    targetnode a' = mx'))) then (\<lambda>cf. True)\<^sub>\<surd> else (\<lambda>cf. False)\<^sub>\<surd>)"
    by(simp add:slice_kind_def Let_def)
  with `distance (targetnode a) mex x` `distance (sourcenode a) mex (x + 1)`
    `targetnode a \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') mex x \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = n')`
  show ?thesis by(auto dest:distance_det)
qed


lemma slice_kind_Pred_empty_obs_not_nearer:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>"
  and "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" 
  and "method_exit mex" and "get_proc (sourcenode a) = get_proc mex"
  and dist:"distance (sourcenode a) mex (x + 1)" "\<not> distance (targetnode a) mex x"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
  have "mex = (THE mex. method_exit mex \<and> get_proc (sourcenode a) = get_proc mex)"
    by(auto intro!:the_equality[THEN sym] intro:method_exit_unique)
  moreover
  from dist have "\<not> (\<exists>x. distance (targetnode a) mex x \<and> 
                            distance (sourcenode a) mex (x + 1))"
    by(fastforce dest:distance_det)
  ultimately show ?thesis using assms by(auto simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_nearer_SOME:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                     distance (targetnode a') m x \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and> 
                                     targetnode a' = n')"
  shows "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
proof -
  from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  have "m = (THE m. m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(rule obs_intra_the_element[THEN sym])
  with assms show ?thesis by(auto simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_nearer_not_SOME:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a \<noteq> (SOME nx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                      distance (targetnode a') m x \<and>
                                      valid_edge a' \<and> intra_kind(kind a') \<and> 
                                      targetnode a' = nx')"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
  have "m = (THE m. m \<in> obs_intra (sourcenode a) (\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>))"
    by(rule obs_intra_the_element[THEN sym])
  with assms show ?thesis by(auto dest:distance_det simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_not_nearer:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = (Q)\<^sub>\<surd>" 
  and in_obs:"m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and dist:"distance (sourcenode a) m (x + 1)" 
           "\<not> distance (targetnode a) m x"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from in_obs have the:"m = (THE m. m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(rule obs_intra_the_element[THEN sym])
  from dist have "\<not> (\<exists>x. distance (targetnode a) m x \<and> 
                            distance (sourcenode a) m (x + 1))"
    by(fastforce dest:distance_det)
  with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>` in_obs the show ?thesis
    by(auto simp:slice_kind_def Let_def)
qed


lemma kind_Predicate_notin_slice_slice_kind_Predicate:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "valid_edge a" and "kind a = (Q)\<^sub>\<surd>"
  obtains Q' where "slice_kind S a = (Q')\<^sub>\<surd>" and "Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True)"
proof(atomize_elim)
  show "\<exists>Q'. slice_kind S a = (Q')\<^sub>\<surd> \<and> (Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True))"
  proof(cases "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
    case True
    from `valid_edge a` have "valid_node (sourcenode a)" by simp
    then obtain as where "sourcenode a -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(fastforce dest:Exit_path)
    then obtain as' mex where "sourcenode a -as'\<rightarrow>\<^sub>\<iota>* mex" and "method_exit mex" 
      by -(erule valid_Exit_path_intra_path)
    from `sourcenode a -as'\<rightarrow>\<^sub>\<iota>* mex` have "get_proc (sourcenode a) = get_proc mex"
      by(rule intra_path_get_procs)
    show ?thesis
    proof(cases "\<exists>x. distance (targetnode a) mex x \<and> 
        distance (sourcenode a) mex (x + 1)")
      case True
      then obtain x where "distance (targetnode a) mex x" 
        and "distance (sourcenode a) mex (x + 1)" by blast
      show ?thesis
      proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') mex x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')")
        case True
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
          `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
          `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
          `distance (targetnode a) mex x` `distance (sourcenode a) mex (x + 1)`
        have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
          by(rule slice_kind_Pred_empty_obs_nearer_SOME)
        thus ?thesis by simp
      next
        case False
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
          `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}`
          `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
          `distance (targetnode a) mex x` `distance (sourcenode a) mex (x + 1)`
        have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
          by(rule slice_kind_Pred_empty_obs_nearer_not_SOME)
        thus ?thesis by simp
      qed
    next
      case False
      from `method_exit mex` `get_proc (sourcenode a) = get_proc mex`
      have "mex = (THE mex. method_exit mex \<and> get_proc (sourcenode a) = get_proc mex)"
        by(auto intro!:the_equality[THEN sym] intro:method_exit_unique)
      with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
        `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}` False
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(auto simp:slice_kind_def Let_def)
      thus ?thesis by simp
    qed
  next
    case False
    then obtain m where "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by blast
    show ?thesis
    proof(cases "\<exists>x. distance (targetnode a) m x \<and> 
        distance (sourcenode a) m (x + 1)")
      case True
      then obtain x where "distance (targetnode a) m x" 
        and "distance (sourcenode a) m (x + 1)" by blast
      show ?thesis
      proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')")
        case True
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
          `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
        have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_SOME)
        thus ?thesis by simp
      next
        case False
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>`
          `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
        have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_not_SOME)
        thus ?thesis by simp
      qed
    next
      case False
      from `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "m = (THE m. m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        by(rule obs_intra_the_element[THEN sym])
      with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = (Q)\<^sub>\<surd>` False
        `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(auto simp:slice_kind_def Let_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma slice_kind_Call:
  "\<lbrakk>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
  \<Longrightarrow> slice_kind S a = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
by(simp add:slice_kind_def)


lemma slice_kind_Call_in_slice:
  "\<lbrakk>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
  \<Longrightarrow> slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
by(simp add:slice_kind_def)


lemma slice_kind_Call_in_slice_Formal_in_not:
  assumes "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "\<forall>x < length fs. Formal_in(targetnode a,x) \<notin> HRB_slice S" 
  shows "slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>replicate (length fs) empty"
proof -
  from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
    by(simp add:slice_kind_def)
  from `\<forall>x < length fs. Formal_in(targetnode a,x) \<notin> HRB_slice S`
  have "cspp (targetnode a) (HRB_slice S) fs = replicate (length fs) empty"
    by(fastforce intro:nth_equalityI csppa_Formal_in_notin_slice simp:cspp_def)
  with `slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)`
  show ?thesis by simp
qed


lemma slice_kind_Call_in_slice_Formal_in_also:
  assumes "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "\<forall>x < length fs. Formal_in(targetnode a,x) \<in> HRB_slice S" 
  shows "slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
proof -
  from `sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
    by(simp add:slice_kind_def)
  from `\<forall>x < length fs. Formal_in(targetnode a,x) \<in> HRB_slice S`
  have "cspp (targetnode a) (HRB_slice S) fs = fs"
    by(fastforce intro:nth_equalityI csppa_Formal_in_in_slice simp:cspp_def)
  with `slice_kind S a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)`
  show ?thesis by simp
qed


lemma slice_kind_Call_intra_notin_slice:
  assumes "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "valid_edge a" 
  and "intra_kind (kind a)" and "valid_edge a'" and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  and "sourcenode a' = sourcenode a"
  shows "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
proof -
  from `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs` obtain a'' 
    where "a'' \<in> get_return_edges a'"
    by(fastforce dest:get_return_edge_call)
  with `valid_edge a'` obtain ax where "valid_edge ax" 
    and "sourcenode ax = sourcenode a'" and " targetnode ax = targetnode a''"
    and "kind ax = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from `valid_edge a'` `kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs`
  have "\<exists>!a''. valid_edge a'' \<and> sourcenode a'' = sourcenode a' \<and> 
    intra_kind(kind a'')"
    by(rule call_only_one_intra_edge)
  with `valid_edge a` `sourcenode a' = sourcenode a` `intra_kind (kind a)`
  have all:"\<forall>a''. valid_edge a'' \<and> sourcenode a'' = sourcenode a' \<and> 
    intra_kind(kind a'') \<longrightarrow> a'' = a" by fastforce
  with `valid_edge ax` `sourcenode ax = sourcenode a'` `kind ax = (\<lambda>cf. False)\<^sub>\<surd>`
  have [simp]:"ax = a" by(fastforce simp:intra_kind_def)
  show ?thesis
  proof(cases "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
    case True
    from `valid_edge a` have "valid_node (sourcenode a)" by simp
    then obtain asx where "sourcenode a -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(fastforce dest:Exit_path)
    then obtain as pex where "sourcenode a-as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
      by -(erule valid_Exit_path_intra_path)
    from `sourcenode a-as\<rightarrow>\<^sub>\<iota>* pex` have "get_proc (sourcenode a) = get_proc pex"
      by(rule intra_path_get_procs)
    from `sourcenode a-as\<rightarrow>\<^sub>\<iota>* pex` obtain x where "distance (sourcenode a) pex x"
      and "x \<le> length as" by(erule every_path_distance)
    from `method_exit pex` have "sourcenode a \<noteq> pex"
    proof(rule method_exit_cases)
      assume "pex = (_Exit_)"
      show ?thesis
      proof
        assume "sourcenode a = pex"
        with `pex = (_Exit_)` have "sourcenode a = (_Exit_)" by simp
        with `valid_edge a` show False by(rule Exit_source)
      qed
    next
      fix ax Qx px fx 
      assume "pex = sourcenode ax" and "valid_edge ax" and "kind ax = Qx\<hookleftarrow>\<^bsub>px\<^esub>fx"
      hence "\<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode ax \<longrightarrow> 
        (\<exists>Qx' fx'. kind a' = Qx'\<hookleftarrow>\<^bsub>px\<^esub>fx')" by -(rule return_edges_only)
      with `valid_edge a` `intra_kind (kind a)` `pex = sourcenode ax`
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
    have "x \<noteq> 0"
    proof
      assume "x = 0"
      with `distance (sourcenode a) pex x` have "sourcenode a = pex"
        by(fastforce elim:distance.cases simp:intra_path_def)
      with `sourcenode a \<noteq> pex` show False by simp
    qed
    with `distance (sourcenode a) pex x` obtain ax' where "valid_edge ax'"
      and "sourcenode a = sourcenode ax'" and "intra_kind(kind ax')"
      and "distance (targetnode ax') pex (x - 1)"
      and Some:"targetnode ax' = (SOME nx. \<exists>a'. sourcenode ax' = sourcenode a' \<and> 
                                          distance (targetnode a') pex (x - 1) \<and>
                                          valid_edge a' \<and> intra_kind(kind a') \<and>
                                          targetnode a' = nx)"
      by(erule distance_successor_distance)
    from `valid_edge ax'` `sourcenode a = sourcenode ax'` `intra_kind(kind ax')`
      `sourcenode a' = sourcenode a` all
    have [simp]:"ax' = a" by fastforce
    from `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind ax = (\<lambda>cf. False)\<^sub>\<surd>`
      True `method_exit pex` `get_proc (sourcenode a) = get_proc pex` `x \<noteq> 0`
      `distance (targetnode ax') pex (x - 1)` `distance (sourcenode a) pex x` Some
    show ?thesis by(fastforce elim:slice_kind_Pred_empty_obs_nearer_SOME)
  next
    case False
    then obtain m where "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
    then obtain as where "sourcenode a-as\<rightarrow>\<^sub>\<iota>* m" and "m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by -(erule obs_intraE)
    from `sourcenode a-as\<rightarrow>\<^sub>\<iota>* m` obtain x where "distance (sourcenode a) m x"
      and "x \<le> length as" by(erule every_path_distance)
    from `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
    have "sourcenode a \<noteq> m" by fastforce
    have "x \<noteq> 0"
    proof
      assume "x = 0"
      with `distance (sourcenode a) m x` have "sourcenode a = m"
        by(fastforce elim:distance.cases simp:intra_path_def)
      with `sourcenode a \<noteq> m` show False by simp
    qed
    with `distance (sourcenode a) m x` obtain ax' where "valid_edge ax'"
      and "sourcenode a = sourcenode ax'" and "intra_kind(kind ax')"
      and "distance (targetnode ax') m (x - 1)"
      and Some:"targetnode ax' = (SOME nx. \<exists>a'. sourcenode ax' = sourcenode a' \<and> 
                                          distance (targetnode a') m (x - 1) \<and>
                                          valid_edge a' \<and> intra_kind(kind a') \<and>
                                          targetnode a' = nx)"
      by(erule distance_successor_distance)
    from `valid_edge ax'` `sourcenode a = sourcenode ax'` `intra_kind(kind ax')`
      `sourcenode a' = sourcenode a` all
    have [simp]:"ax' = a" by fastforce
    from `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind ax = (\<lambda>cf. False)\<^sub>\<surd>`
      `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `x \<noteq> 0`
      `distance (targetnode ax') m (x - 1)` `distance (sourcenode a) m x` Some
    show ?thesis by(fastforce elim:slice_kind_Pred_obs_nearer_SOME)
  qed
qed


lemma slice_kind_Return:
  "\<lbrakk>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<rbrakk>
  \<Longrightarrow> slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
by(simp add:slice_kind_def)


lemma slice_kind_Return_in_slice:
  "\<lbrakk>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; 
   (p,ins,outs) \<in> set procs\<rbrakk>
  \<Longrightarrow> slice_kind S a = Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
by(simp add:slice_kind_def,unfold formal_out_THE,simp)


lemma length_transfer_kind_slice_kind:
  assumes "valid_edge a" and "length s\<^sub>1 = length s\<^sub>2"
  and "transfer (kind a) s\<^sub>1 = s\<^sub>1'" and "transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'"
  shows "length s\<^sub>1' = length s\<^sub>2'"
proof(cases "kind a" rule:edge_kind_cases)
  case Intra
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with Intra assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_intra_kind_in_slice simp:intra_kind_def)+
  next
    case False
    with Intra assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_kind_Upd 
        elim:kind_Predicate_notin_slice_slice_kind_Predicate simp:intra_kind_def)+
  qed
next
  case (Call Q r p fs)
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with Call assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_kind_Call_in_slice)+
  next
    case False
    with Call assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_kind_Call)+
  qed
next
  case (Return Q p f)
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    from Return `valid_edge a` obtain a' Q' r fs 
      where "valid_edge a'" and "kind a' = Q':r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      by -(drule return_needs_call,auto)
    then obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    with True `valid_edge a` Return assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_kind_Return_in_slice split:list.split)+
  next    
    case False
    with Return assms show ?thesis
      by(cases s\<^sub>1)(cases s\<^sub>2,auto dest:slice_kind_Return split:list.split)+
  qed
qed


subsection {* The sliced graph of a deterministic CFG is still deterministic *} 

lemma only_one_SOME_edge:
  assumes "valid_edge a" and "intra_kind(kind a)" and "distance (targetnode a) mex x"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and>
               valid_edge a' \<and> intra_kind(kind a') \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              distance (targetnode a') mex x \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and>
                                              targetnode a' = n')"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and>
             valid_edge a' \<and> intra_kind(kind a') \<and>
             targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            distance (targetnode a') mex x \<and>
                                            valid_edge a' \<and> intra_kind(kind a') \<and>
                                            targetnode a' = n')"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and>
                valid_edge a' \<and> intra_kind(kind a') \<and>
                targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') mex x \<and>
                                               valid_edge a' \<and> intra_kind(kind a') \<and>
                                               targetnode a' = n')) =
      (\<exists>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and>
                 valid_edge a' \<and> intra_kind(kind a') \<and> targetnode a' = n')"
      apply(unfold some_eq_ex[of "\<lambda>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            distance (targetnode a') mex x \<and>
                                            valid_edge a' \<and> intra_kind(kind a') \<and>
                                            targetnode a' = n'"])
      by simp
    also have "\<dots>" 
      using `valid_edge a` `intra_kind(kind a)` `distance (targetnode a) mex x` 
      by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and>
    valid_edge a' \<and> intra_kind(kind a') \<and>
    targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   distance (targetnode a') mex x \<and>
                                   valid_edge a' \<and> intra_kind(kind a') \<and>
                                   targetnode a' = n')"
    and "sourcenode a = sourcenode ax \<and> distance (targetnode ax) mex x \<and>
    valid_edge ax \<and> intra_kind(kind ax) \<and>
    targetnode ax = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   distance (targetnode a') mex x \<and>
                                   valid_edge a' \<and> intra_kind(kind a') \<and>
                                   targetnode a' = n')"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma slice_kind_only_one_True_edge:
  assumes "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'" 
  and "valid_edge a" and "valid_edge a'" and "intra_kind (kind a)" 
  and "intra_kind (kind a')" and "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
  shows "slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from assms obtain Q Q' where "kind a = (Q)\<^sub>\<surd>"
    and "kind a' = (Q')\<^sub>\<surd>" and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (Q)\<^sub>\<surd>` have "Q = (\<lambda>s. True)"
      by(simp add:slice_kind_def Let_def)
    with det have "Q' = (\<lambda>s. False)" by(simp add:fun_eq_iff)
    with True `kind a' = (Q')\<^sub>\<surd>` `sourcenode a = sourcenode a'` show ?thesis
      by(simp add:slice_kind_def Let_def)
  next
    case False
    hence "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    thus ?thesis
    proof(cases "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
      case True
      with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>`
        `kind a = (Q)\<^sub>\<surd>`
      obtain mex x where mex:"mex = (THE mex. method_exit mex \<and> 
        get_proc (sourcenode a) = get_proc mex)"
        and dist:"distance (targetnode a) mex x" "distance (sourcenode a) mex (x + 1)"
        and target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') mex x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
      from `valid_edge a` `intra_kind (kind a)` `distance (targetnode a) mex x`
      have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') mex x \<and> 
        valid_edge a' \<and> intra_kind(kind a') \<and>
        targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                       distance (targetnode a') mex x \<and>
                                       valid_edge a' \<and> intra_kind(kind a') \<and>
                                       targetnode a' = n')"
        by(rule only_one_SOME_edge)
      have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                           distance (targetnode a') mex x \<and>
                                           valid_edge a' \<and> intra_kind(kind a') \<and>
                                           targetnode a' = n')"
      proof(rule ccontr)
        assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') mex x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')"
        hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              distance (targetnode a') mex x \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and>
                                              targetnode a' = n')"
          by simp
        with ex1 target `sourcenode a = sourcenode a'` `valid_edge a` `valid_edge a'`
          `intra_kind(kind a)` `intra_kind(kind a')` `distance (targetnode a) mex x`
        have "a = a'" by fastforce
        with `targetnode a \<noteq> targetnode a'` show False by simp
      qed
      with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` True `kind a' = (Q')\<^sub>\<surd>`
        `sourcenode a = sourcenode a'` mex dist
      show ?thesis by(auto dest:distance_det 
        simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
    next
      case False
      hence "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}" .
      then obtain m where "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by auto
      hence "m = (THE m. m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        by(auto dest:obs_intra_the_element)
      with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
        `obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}` 
        `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (Q)\<^sub>\<surd>`
      obtain x x' where "distance (targetnode a) m x" 
        "distance (sourcenode a) m (x + 1)"
        and target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
      show ?thesis
      proof(cases "distance (targetnode a') m x")
        case False
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` `kind a' = (Q')\<^sub>\<surd>`
          `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          `sourcenode a = sourcenode a'` show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_not_nearer)
      next
        case True
        from `valid_edge a` `intra_kind(kind a)` `distance (targetnode a) m x`
          `distance (sourcenode a) m (x + 1)`
        have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> 
               distance (targetnode a') m x \<and> valid_edge a' \<and> intra_kind(kind a') \<and> 
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') m x \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and> 
                                              targetnode a' = nx)"
          by -(rule only_one_SOME_dist_edge)
        have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m x \<and>
                                               valid_edge a' \<and> intra_kind(kind a') \<and> 
                                               targetnode a' = n')"
        proof(rule ccontr)
          assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = n')"
          hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                distance (targetnode a') m x \<and>
                                                valid_edge a' \<and> intra_kind(kind a') \<and>
                                                targetnode a' = n')"
            by simp
          with ex1 target `sourcenode a = sourcenode a'` 
            `valid_edge a` `valid_edge a'` `intra_kind(kind a)` `intra_kind(kind a')`
            `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          have "a = a'" by auto
          with `targetnode a \<noteq> targetnode a'` show False by simp
        qed
        with `sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>` 
          `kind a' = (Q')\<^sub>\<surd>` `m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          True `sourcenode a = sourcenode a'` show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_nearer_not_SOME)
      qed
    qed
  qed
qed


lemma slice_deterministic:
  assumes "valid_edge a" and "valid_edge a'"
  and "intra_kind (kind a)" and "intra_kind (kind a')"
  and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
  obtains Q Q' where "slice_kind S a = (Q)\<^sub>\<surd>" and "slice_kind S a' = (Q')\<^sub>\<surd>"
  and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
proof(atomize_elim)
  from assms obtain Q Q' 
    where "kind a = (Q)\<^sub>\<surd>" and "kind a' = (Q')\<^sub>\<surd>" 
    and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  show "\<exists>Q Q'. slice_kind S a = (Q)\<^sub>\<surd> \<and> slice_kind S a' = (Q')\<^sub>\<surd> \<and> 
                (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with `kind a = (Q)\<^sub>\<surd>` have "slice_kind S a = (Q)\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    from True `kind a' = (Q')\<^sub>\<surd>` `sourcenode a = sourcenode a'`
    have "slice_kind S a' = (Q')\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    with `slice_kind S a = (Q)\<^sub>\<surd>` det show ?thesis by blast
  next
    case False
    with `kind a = (Q)\<^sub>\<surd>` 
    have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd> \<or> slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    thus ?thesis
    proof
      assume true:"slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
      with `sourcenode a = sourcenode a'` `targetnode a \<noteq> targetnode a'`
        `valid_edge a` `valid_edge a'` `intra_kind (kind a)` `intra_kind (kind a')`
      have "slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
        by(rule slice_kind_only_one_True_edge)
      with true show ?thesis by simp
    next
      assume false:"slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
      from False `kind a' = (Q')\<^sub>\<surd>` `sourcenode a = sourcenode a'`
      have "slice_kind S a' = (\<lambda>s. True)\<^sub>\<surd> \<or> slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
        by(simp add:slice_kind_def Let_def)
      with false show ?thesis by auto
    qed
  qed
qed

end

end
