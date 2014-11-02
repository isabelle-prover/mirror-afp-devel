section {* Static backward slice *}

theory Slice 
  imports Observable Distance DataDependence "../Basic/SemanticsCFG"  
begin

locale BackwardSlice = 
  CFG_wf sourcenode targetnode kind valid_edge Entry Def Use state_val
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val" +
  fixes backward_slice :: "'node set \<Rightarrow> 'node set"
  assumes valid_nodes:"n \<in> backward_slice S \<Longrightarrow> valid_node n"
  and refl:"\<lbrakk>valid_node n; n \<in> S\<rbrakk> \<Longrightarrow> n \<in> backward_slice S"
  and dd_closed:"\<lbrakk>n' \<in> backward_slice S; n influences V in n'\<rbrakk> 
  \<Longrightarrow> n \<in> backward_slice S"
  and obs_finite:"finite (obs n (backward_slice S))"
  and obs_singleton:"card (obs n (backward_slice S)) \<le> 1"

begin

lemma slice_n_in_obs:
  "n \<in> backward_slice S \<Longrightarrow> obs n (backward_slice S) = {n}"
by(fastforce intro!:n_in_obs dest:valid_nodes)

lemma obs_singleton_disj: 
  "(\<exists>m. obs n (backward_slice S) = {m}) \<or> obs n (backward_slice S) = {}"
proof -
  have "finite(obs n (backward_slice S))" by(rule obs_finite)
  show ?thesis
  proof(cases "card(obs n (backward_slice S)) = 0")
    case True
    with `finite(obs n (backward_slice S))` have "obs n (backward_slice S) = {}"
      by simp
    thus ?thesis by simp
  next
    case False
    have "card(obs n (backward_slice S)) \<le> 1" by(rule obs_singleton)
    with False have "card(obs n (backward_slice S)) = 1"
      by simp
    hence "\<exists>m. obs n (backward_slice S) = {m}" by(fastforce dest:card_eq_SucD)
    thus ?thesis by simp
  qed
qed


lemma obs_singleton_element:
  assumes "m \<in> obs n (backward_slice S)" shows "obs n (backward_slice S) = {m}"
proof -
  have "(\<exists>m. obs n (backward_slice S) = {m}) \<or> obs n (backward_slice S) = {}"
    by(rule obs_singleton_disj)
  with `m \<in> obs n (backward_slice S)` show ?thesis by fastforce
qed


lemma obs_the_element: 
  "m \<in> obs n (backward_slice S) \<Longrightarrow> (THE m. m \<in> obs n (backward_slice S)) = m"
by(fastforce dest:obs_singleton_element)


subsection {* Traversing the sliced graph *}

text {* @{text "slice_kind S a"} conforms to @{term "kind a"} in the
  sliced graph *}

definition slice_kind :: "'node set \<Rightarrow> 'edge \<Rightarrow> 'state edge_kind"
  where "slice_kind S a = (let S' = backward_slice S; n = sourcenode a in 
  (if sourcenode a \<in> S' then kind a
   else (case kind a of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> 
    (if obs (sourcenode a) S' = {} then 
      (let nx = (SOME n'. \<exists>a'. n = sourcenode a' \<and> valid_edge a' \<and> targetnode a' = n')
      in (if (targetnode a = nx) then (\<lambda>s. True)\<^sub>\<surd> else (\<lambda>s. False)\<^sub>\<surd>))
     else (let m = THE m. m \<in> obs n S' in 
       (if (\<exists>x. distance (targetnode a) m x \<and> distance n m (x + 1) \<and>
            (targetnode a = (SOME nx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') m x \<and>
                                     valid_edge a' \<and> targetnode a' = nx'))) 
          then (\<lambda>s. True)\<^sub>\<surd> else (\<lambda>s. False)\<^sub>\<surd>
       ))
     ))
  ))"


definition
  slice_kinds :: "'node set \<Rightarrow> 'edge list \<Rightarrow> 'state edge_kind list"
  where "slice_kinds S as \<equiv> map (slice_kind S) as"


lemma slice_kind_in_slice:
  "sourcenode a \<in> backward_slice S \<Longrightarrow> slice_kind S a = kind a"
by(simp add:slice_kind_def)


lemma slice_kind_Upd:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = \<Up>f\<rbrakk> \<Longrightarrow> slice_kind S a = \<Up>id"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_empty_obs_SOME:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = (Q)\<^sub>\<surd>; 
    obs (sourcenode a) (backward_slice S) = {}; 
    targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                                  targetnode a' = n')\<rbrakk>
  \<Longrightarrow> slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_empty_obs_not_SOME:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = (Q)\<^sub>\<surd>; 
    obs (sourcenode a) (backward_slice S) = {}; 
    targetnode a \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                                  targetnode a' = n')\<rbrakk>
  \<Longrightarrow> slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_obs_nearer_SOME:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs (sourcenode a) (backward_slice S)"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                          distance (targetnode a') m x \<and>
                                          valid_edge a' \<and> targetnode a' = n')"
  shows "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
proof -
  from `m \<in> obs (sourcenode a) (backward_slice S)`
  have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  with assms show ?thesis
    by(fastforce simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_nearer_not_SOME:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs (sourcenode a) (backward_slice S)"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a \<noteq> (SOME nx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                          distance (targetnode a') m x \<and>
                                          valid_edge a' \<and> targetnode a' = nx')"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from `m \<in> obs (sourcenode a) (backward_slice S)`
  have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  with assms show ?thesis
    by(fastforce dest:distance_det simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_not_nearer:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and in_obs:"m \<in> obs (sourcenode a) (backward_slice S)"
  and dist:"distance (sourcenode a) m (x + 1)" 
           "\<not> distance (targetnode a) m x"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from in_obs have the:"m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  from dist have "\<not> (\<exists>x. distance (targetnode a) m x \<and> 
                            distance (sourcenode a) m (x + 1))"
    by(fastforce dest:distance_det)
  with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>` in_obs the show ?thesis
    by(fastforce simp:slice_kind_def Let_def)
qed


lemma kind_Predicate_notin_slice_slice_kind_Predicate:
  assumes "kind a = (Q)\<^sub>\<surd>" and "sourcenode a \<notin> backward_slice S"
  obtains Q' where "slice_kind S a = (Q')\<^sub>\<surd>" and "Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True)"
proof(atomize_elim)
  show "\<exists>Q'. slice_kind S a = (Q')\<^sub>\<surd> \<and> (Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True))"
  proof(cases "obs (sourcenode a) (backward_slice S) = {}")
    case True
    show ?thesis
    proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               valid_edge a' \<and> targetnode a' = n')")
      case True
      with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>`
        `obs (sourcenode a) (backward_slice S) = {}`
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>" by(rule slice_kind_Pred_empty_obs_SOME)
      thus ?thesis by simp
    next
      case False
      with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>`
        `obs (sourcenode a) (backward_slice S) = {}`
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(rule slice_kind_Pred_empty_obs_not_SOME)
      thus ?thesis by simp
    qed
  next
    case False
    then obtain m where "m \<in> obs (sourcenode a) (backward_slice S)" by blast
    show ?thesis
    proof(cases "\<exists>x. distance (targetnode a) m x \<and> 
        distance (sourcenode a) m (x + 1)")
      case True
      then obtain x where "distance (targetnode a) m x" 
        and "distance (sourcenode a) m (x + 1)" by blast
      show ?thesis
      proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')")
        case True
        with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>`
          `m \<in> obs (sourcenode a) (backward_slice S)`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
        have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_SOME)
        thus ?thesis by simp
      next
        case False
        with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>`
          `m \<in> obs (sourcenode a) (backward_slice S)`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
        have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_not_SOME)
        thus ?thesis by simp
      qed
    next
      case False
      from `m \<in> obs (sourcenode a) (backward_slice S)`
      have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
        by(rule obs_the_element[THEN sym])
      with `sourcenode a \<notin> backward_slice S` `kind a = (Q)\<^sub>\<surd>` False
        `m \<in> obs (sourcenode a) (backward_slice S)`
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(fastforce simp:slice_kind_def Let_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma only_one_SOME_edge:
  assumes "valid_edge a"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
             targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n')"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               valid_edge a' \<and> targetnode a' = n')) =
      (\<exists>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and> targetnode a' = n')"
      apply(unfold some_eq_ex[of "\<lambda>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n'"])
      by simp
    also have "\<dots>" using `valid_edge a` by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
    targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   valid_edge a' \<and> targetnode a' = n')"
    and "sourcenode a = sourcenode ax \<and> valid_edge ax \<and>
    targetnode ax = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                              valid_edge a' \<and> targetnode a' = n')"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma slice_kind_only_one_True_edge:
  assumes "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'" 
  and "valid_edge a" and "valid_edge a'" and "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
  shows "slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from assms obtain Q Q' where "kind a = (Q)\<^sub>\<surd>"
    and "kind a' = (Q')\<^sub>\<surd>" and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from `valid_edge a` have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
    by(rule only_one_SOME_edge)
  show ?thesis
  proof(cases "sourcenode a \<in> backward_slice S")
    case True
    with `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (Q)\<^sub>\<surd>` have "Q = (\<lambda>s. True)"
      by(simp add:slice_kind_def Let_def)
    with det have "Q' = (\<lambda>s. False)" by(simp add:fun_eq_iff)
    with True `kind a' = (Q')\<^sub>\<surd>` `sourcenode a = sourcenode a'` show ?thesis
      by(simp add:slice_kind_def Let_def)
  next
    case False
    hence "sourcenode a \<notin> backward_slice S" by simp
    thus ?thesis
    proof(cases "obs (sourcenode a) (backward_slice S) = {}")
      case True
      with `sourcenode a \<notin> backward_slice S` `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>`
        `kind a = (Q)\<^sub>\<surd>`
      have target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 valid_edge a' \<and> targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
      have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n')"
      proof(rule ccontr)
        assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 valid_edge a' \<and> targetnode a' = n')"
        hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
          by simp
        with ex1 target `sourcenode a = sourcenode a'` `valid_edge a`
          `valid_edge a'` have "a = a'" by blast
        with `targetnode a \<noteq> targetnode a'` show False by simp
      qed
      with `sourcenode a \<notin> backward_slice S` True `kind a' = (Q')\<^sub>\<surd>`
        `sourcenode a = sourcenode a'` show ?thesis 
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
    next
      case False
      hence "obs (sourcenode a) (backward_slice S) \<noteq> {}" .
      then obtain m where "m \<in> obs (sourcenode a) (backward_slice S)" by auto
      hence "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
        by(auto dest:obs_the_element)
      with `sourcenode a \<notin> backward_slice S` 
        `obs (sourcenode a) (backward_slice S) \<noteq> {}` 
        `slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>` `kind a = (Q)\<^sub>\<surd>`
      obtain x x' where "distance (targetnode a) m x" 
        "distance (sourcenode a) m (x + 1)"
        and target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:split_if_asm)
      show ?thesis
      proof(cases "distance (targetnode a') m x")
        case False
        with `sourcenode a \<notin> backward_slice S` `kind a' = (Q')\<^sub>\<surd>`
          `m \<in> obs (sourcenode a) (backward_slice S)`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          `sourcenode a = sourcenode a'` show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_not_nearer)
      next
        case True
        from `valid_edge a` `distance (targetnode a) m x`
          `distance (sourcenode a) m (x + 1)`
        have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> 
               distance (targetnode a') m x \<and> valid_edge a' \<and>
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') m x \<and>
                                              valid_edge a' \<and> targetnode a' = nx)"
          by(fastforce intro!:only_one_SOME_dist_edge)
        have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m x \<and>
                                               valid_edge a' \<and> targetnode a' = n')"
        proof(rule ccontr)
          assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')"
          hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                distance (targetnode a') m x \<and>
                                                valid_edge a' \<and> targetnode a' = n')"
            by simp
          with ex1 target `sourcenode a = sourcenode a'` 
            `valid_edge a` `valid_edge a'` 
            `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          have "a = a'" by auto
          with `targetnode a \<noteq> targetnode a'` show False by simp
        qed
        with `sourcenode a \<notin> backward_slice S` 
          `kind a' = (Q')\<^sub>\<surd>` `m \<in> obs (sourcenode a) (backward_slice S)`
          `distance (targetnode a) m x` `distance (sourcenode a) m (x + 1)`
          True `sourcenode a = sourcenode a'` show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_nearer_not_SOME)
      qed
    qed
  qed
qed


lemma slice_deterministic:
  assumes "valid_edge a" and "valid_edge a'"
  and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
  obtains Q Q' where "slice_kind S a = (Q)\<^sub>\<surd>" and "slice_kind S a' = (Q')\<^sub>\<surd>"
  and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
proof(atomize_elim)
  from assms obtain Q Q' 
    where "kind a = (Q)\<^sub>\<surd>" and "kind a' = (Q')\<^sub>\<surd>" 
    and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from `valid_edge a` have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
    by(rule only_one_SOME_edge)
  show "\<exists>Q Q'. slice_kind S a = (Q)\<^sub>\<surd> \<and> slice_kind S a' = (Q')\<^sub>\<surd> \<and> 
                (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
  proof(cases "sourcenode a \<in> backward_slice S")
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
        `valid_edge a` `valid_edge a'`
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




subsection {* Observable and silent moves *}

inductive silent_move :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') -_\<rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where silent_moveI:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; sourcenode a \<notin> backward_slice S; 
    valid_edge a\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (sourcenode a,s) -a\<rightarrow>\<^sub>\<tau> (targetnode a,s')"


inductive silent_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51)

  where silent_moves_Nil: "S,f \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n,s)"

  | silent_moves_Cons:
  "\<lbrakk>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s'); S,f \<turnstile> (n',s') =as\<Rightarrow>\<^sub>\<tau> (n'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (n,s) =a#as\<Rightarrow>\<^sub>\<tau> (n'',s'')"


lemma silent_moves_obs_slice:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); nx \<in> obs n' (backward_slice S)\<rbrakk>
  \<Longrightarrow> nx \<in> obs n (backward_slice S)"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  from `nx \<in> obs n'' (backward_slice S)`
    `nx \<in> obs n'' (backward_slice S) \<Longrightarrow> nx \<in> obs n' (backward_slice S)`
  have obs:"nx \<in> obs n' (backward_slice S)" by simp
  from `S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')`
  have "n = sourcenode a" and "n' = targetnode a" and "valid_edge a" 
    and "n \<notin> (backward_slice S)"
    by(auto elim:silent_move.cases)
  hence "obs n' (backward_slice S) \<subseteq> obs n (backward_slice S)"
    by simp(rule edge_obs_subset,simp+)
  with obs show ?case by blast
qed


lemma silent_moves_preds_transfers_path:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); valid_node n\<rbrakk> 
  \<Longrightarrow> preds (map f as) s \<and> transfers (map f as) s = s' \<and> n -as\<rightarrow>* n'"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by(simp add:path.empty_path)
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  note IH = `valid_node n' \<Longrightarrow>
    preds (map f as) s' \<and> transfers (map f as) s' = s'' \<and> n' -as\<rightarrow>* n''`
  from `S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')` have "pred (f a) s" and "transfer (f a) s = s'"
    and "n = sourcenode a" and "n' = targetnode a" and "valid_edge a"
    by(auto elim:silent_move.cases)
  from `n' = targetnode a` `valid_edge a` have "valid_node n'" by simp
  from IH[OF this] have "preds (map f as) s'" and "transfers (map f as) s' = s''"
    and "n' -as\<rightarrow>* n''" by simp_all
  from `n = sourcenode a` `n' = targetnode a` `valid_edge a` `n' -as\<rightarrow>* n''`
  have "n -a#as\<rightarrow>* n''" by(fastforce intro:Cons_path)
  with `pred (f a) s` `preds (map f as) s'` `transfer (f a) s = s'` 
    `transfers (map f as) s' = s''` show ?case by simp
qed


lemma obs_silent_moves:
  assumes "obs n (backward_slice S) = {n'}"
  obtains as where "S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
proof(atomize_elim)
  from `obs n (backward_slice S) = {n'}` 
  have "n' \<in> obs n (backward_slice S)" by simp
  then obtain as where "n -as\<rightarrow>* n'" 
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
    and "n' \<in> (backward_slice S)" by(erule obsE)
  from `n -as\<rightarrow>* n'` obtain x where "distance n n' x" and "x \<le> length as"
    by(erule every_path_distance)
  from `distance n n' x` `n' \<in> obs n (backward_slice S)` 
  show "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
  proof(induct x arbitrary:n s rule:nat.induct)
    fix n s assume "distance n n' 0"
    then obtain as' where "n -as'\<rightarrow>* n'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "n -[]\<rightarrow>* n'" by(cases as) auto
    hence "n = n'" by(fastforce elim:path.cases)
    hence "S,slice_kind S \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n',s)" by(fastforce intro:silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)" by blast
  next
    fix x n s 
    assume "distance n n' (Suc x)" and "n' \<in> obs n (backward_slice S)"
      and IH:"\<And>n s. \<lbrakk>distance n n' x; n' \<in> obs n (backward_slice S)\<rbrakk> 
              \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
    from `n' \<in> obs n (backward_slice S)`
    have "valid_node n" by(rule in_obs_valid)
    with `distance n n' (Suc x)`
    have "n \<noteq> n'" by(fastforce elim:distance.cases dest:empty_path)
    have "n \<notin> backward_slice S"
    proof
      assume isin:"n \<in> backward_slice S"
      with `valid_node n` have "obs n (backward_slice S) = {n}"
        by(fastforce intro!:n_in_obs)
      with `n' \<in> obs n (backward_slice S)` `n \<noteq> n'` show False by simp
    qed
    from `distance n n' (Suc x)` obtain a where "valid_edge a" 
      and "n = sourcenode a" and "distance (targetnode a) n' x"
      and target:"targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') n' x \<and>
                                     valid_edge a' \<and> targetnode a' = nx)"
      by -(erule distance_successor_distance,simp+)
    from `n' \<in> obs n (backward_slice S)`
    have "obs n (backward_slice S) = {n'}"
      by(rule obs_singleton_element)
    with `valid_edge a` `n \<notin> backward_slice S` `n = sourcenode a`
    have disj:"obs (targetnode a) (backward_slice S) = {} \<or> 
               obs (targetnode a) (backward_slice S) = {n'}"
      by -(drule_tac S="backward_slice S" in edge_obs_subset,auto)
    from `distance (targetnode a) n' x` obtain asx where "targetnode a -asx\<rightarrow>* n'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>* n' \<longrightarrow> x \<le> length as'" 
      by(auto elim:distance.cases)
    from `targetnode a -asx\<rightarrow>* n'` `n' \<in> (backward_slice S)`
    obtain m where "\<exists>m. m \<in> obs (targetnode a) (backward_slice S)"
      by(fastforce elim:path_ex_obs)
    with disj have "n' \<in> obs (targetnode a) (backward_slice S)" by fastforce
    from IH[OF `distance (targetnode a) n' x` this,of "transfer (slice_kind S a) s"]
    obtain asx' where 
    moves:"S,slice_kind S \<turnstile> (targetnode a,transfer (slice_kind S a) s) =asx'\<Rightarrow>\<^sub>\<tau> 
                               (n',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      case (Update f)
      with `n \<notin> backward_slice S` `n = sourcenode a` have "slice_kind S a = \<Up>id" 
        by(fastforce intro:slice_kind_Upd)
      thus ?thesis by simp
    next
      case (Predicate Q)
      with `n \<notin> backward_slice S` `n = sourcenode a`
        `n' \<in> obs n (backward_slice S)` `distance (targetnode a) n' x`
        `distance n n' (Suc x)` target
      have "slice_kind S a =  (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with `n \<notin> backward_slice S` `n = sourcenode a` `valid_edge a`
    have "S,slice_kind S \<turnstile> (sourcenode a,s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a,transfer (slice_kind S a) s)"
      by(fastforce intro:silent_moveI)
    with moves `transfer (slice_kind S a) s = s` `n = sourcenode a`
    have "S,slice_kind S \<turnstile> (n,s) =a#asx'\<Rightarrow>\<^sub>\<tau> (n',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)" by blast
  qed
qed


inductive observable_move ::
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') -_\<rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where observable_moveI:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; sourcenode a \<in> backward_slice S; 
    valid_edge a\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (sourcenode a,s) -a\<rightarrow> (targetnode a,s')"


inductive observable_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 

  where observable_moves_snoc:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (n,s) =as@[a]\<Rightarrow> (n'',s'')"


lemma observable_move_notempty:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s'); as = []\<rbrakk> \<Longrightarrow> False"
by(induct rule:observable_moves.induct,simp)


lemma silent_move_observable_moves:
  "\<lbrakk>S,f \<turnstile> (n'',s'') =as\<Rightarrow> (n',s'); S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (n,s) =a#as\<Rightarrow> (n',s')"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f nx sx as n' s' a' n'' s'')
  from `S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (nx,sx)` `S,f \<turnstile> (nx,sx) =as\<Rightarrow>\<^sub>\<tau> (n',s')`
  have "S,f \<turnstile> (n,s) =a#as\<Rightarrow>\<^sub>\<tau> (n',s')" by(rule silent_moves_Cons)
  with `S,f \<turnstile> (n',s') -a'\<rightarrow> (n'',s'')`
  have "S,f \<turnstile> (n,s) =(a#as)@[a']\<Rightarrow> (n'',s'')"
    by -(rule observable_moves.observable_moves_snoc)
  thus ?case by simp
qed


lemma observable_moves_preds_transfers_path:
  "S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')
  \<Longrightarrow> preds (map f as) s \<and> transfers (map f as) s = s' \<and> n -as\<rightarrow>* n'"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f n s as n' s' a n'' s'')
  have "valid_node n"
  proof(cases as)
    case Nil
    with `S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')` have "n = n'" and "s = s'"
      by(auto elim:silent_moves.cases)
    with `S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')` show ?thesis
      by(fastforce elim:observable_move.cases)
  next
    case (Cons a' as')
    with `S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')` show ?thesis
      by(fastforce elim:silent_moves.cases silent_move.cases)
  qed
  with `S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')`
  have "preds (map f as) s" and "transfers (map f as) s = s'"
    and "n -as\<rightarrow>* n'" by(auto dest:silent_moves_preds_transfers_path)
  from `S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')` have "pred (f a) s'" 
    and "transfer (f a) s' = s''" and "n' = sourcenode a" and "n'' = targetnode a" 
    and "valid_edge a"
    by(auto elim:observable_move.cases)
  from `n' = sourcenode a` `n'' = targetnode a` `valid_edge a`
  have "n' -[a]\<rightarrow>* n''" by(fastforce intro:path.intros)
  with `n -as\<rightarrow>* n'` have "n -as@[a]\<rightarrow>* n''" by(rule path_Append)
  with `preds (map f as) s` `pred (f a) s'` `transfer (f a) s' = s''`
    `transfers (map f as) s = s'`
  show ?case by(simp add:transfers_split preds_split)
qed




subsection {* Relevant variables *}

inductive_set relevant_vars :: "'node set \<Rightarrow> 'node \<Rightarrow> 'var set" ("rv _")
for S :: "'node set" and n :: "'node"

where rvI:
  "\<lbrakk>n -as\<rightarrow>* n'; n' \<in> backward_slice S; V \<in> Use n';
    \<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx\<rbrakk>
  \<Longrightarrow> V \<in> rv S n"


lemma rvE:
  assumes rv:"V \<in> rv S n"
  obtains as n' where "n -as\<rightarrow>* n'" and "n' \<in> backward_slice S" and "V \<in> Use n'"
  and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx"
using rv
by(atomize_elim,auto elim!:relevant_vars.cases)



lemma eq_obs_in_rv:
  assumes obs_eq:"obs n (backward_slice S) = obs n' (backward_slice S)" 
  and "x \<in> rv S n" shows "x \<in> rv S n'"
proof -
  from `x \<in> rv S n` obtain as m 
    where "n -as\<rightarrow>* m" and "m \<in> backward_slice S" and "x \<in> Use m"
    and "\<forall>nx\<in>set (sourcenodes as). x \<notin> Def nx"
    by(erule rvE)
  from `n -as\<rightarrow>* m` have "valid_node m" by(fastforce dest:path_valid_node)
  from `n -as\<rightarrow>* m` `m \<in> backward_slice S` 
  have "\<exists>nx as' as''. nx \<in> obs n (backward_slice S) \<and> n -as'\<rightarrow>* nx \<and> 
                                     nx -as''\<rightarrow>* m \<and> as = as'@as''"
  proof(cases "\<forall>nx \<in> set(sourcenodes as). nx \<notin> backward_slice S")
    case True
    with `n -as\<rightarrow>* m` `m \<in> backward_slice S` have "m \<in> obs n (backward_slice S)"
      by -(rule obs_elem)
    with `n -as\<rightarrow>* m` `valid_node m` show ?thesis by(blast intro:empty_path)
  next
    case False
    hence "\<exists>nx \<in> set(sourcenodes as). nx \<in> backward_slice S" by simp
    then obtain nx' ns ns' where "sourcenodes as = ns@nx'#ns'"
      and "nx' \<in> backward_slice S" 
      and "\<forall>x \<in> set ns. x \<notin> backward_slice S"
      by(fastforce elim!:split_list_first_propE)
    from `sourcenodes as = ns@nx'#ns'`
    obtain as' a' as'' where "ns = sourcenodes as'"
      and "as = as'@a'#as''" and "sourcenode a' = nx'"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from `n -as\<rightarrow>* m` `as = as'@a'#as''` `sourcenode a' = nx'`
    have "n -as'\<rightarrow>* nx'" and "valid_edge a'" and "targetnode a' -as''\<rightarrow>* m"
      by(fastforce dest:path_split)+
    with `sourcenode a' = nx'` have "nx' -a'#as''\<rightarrow>* m" by(fastforce intro:Cons_path)
    from `n -as'\<rightarrow>* nx'` `nx' \<in> backward_slice S`
      `\<forall>x \<in> set ns. x \<notin> backward_slice S` `ns = sourcenodes as'` 
    have "nx' \<in> obs n (backward_slice S)" 
      by(fastforce intro:obs_elem)
    with `n -as'\<rightarrow>* nx'` `nx' -a'#as''\<rightarrow>* m` `as = as'@a'#as''` show ?thesis by blast
  qed
  then obtain nx as' as'' where "nx \<in> obs n (backward_slice S)"
    and "n -as'\<rightarrow>* nx" and "nx -as''\<rightarrow>* m" and "as = as'@as''"
    by blast
  from `nx \<in> obs n (backward_slice S)` obs_eq 
  have "nx \<in> obs n' (backward_slice S)" by auto
  then obtain asx where "n' -asx\<rightarrow>* nx" 
    and "\<forall>ni \<in> set(sourcenodes asx). ni \<notin> backward_slice S" 
    and "nx \<in> backward_slice S"
    by(erule obsE)
  from `as = as'@as''` `\<forall>nx\<in>set (sourcenodes as). x \<notin> Def nx` 
  have "\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni"
    by(auto simp:sourcenodes_def)
  from `\<forall>ni \<in> set(sourcenodes asx). ni \<notin> backward_slice S` `n' -asx\<rightarrow>* nx`
  have "\<forall>ni \<in> set(sourcenodes asx). x \<notin> Def ni"
  proof(induct asx arbitrary:n')
    case Nil thus ?case by(simp add:sourcenodes_def)
  next
    case (Cons ax' asx')
    note IH = `\<And>n'. \<lbrakk>\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> backward_slice S; 
      n' -asx'\<rightarrow>* nx\<rbrakk> 
        \<Longrightarrow> \<forall>ni\<in>set (sourcenodes asx'). x \<notin> Def ni`
    from `n' -ax'#asx'\<rightarrow>* nx` have "n' -[]@ax'#asx'\<rightarrow>* nx" by simp
    hence "targetnode ax' -asx'\<rightarrow>* nx" and "n' = sourcenode ax'"
      by(fastforce dest:path_split)+
    from `\<forall>ni\<in>set (sourcenodes (ax'#asx')). ni \<notin> backward_slice S`
    have all:"\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> backward_slice S" 
      and "sourcenode ax' \<notin> backward_slice S"
      by(auto simp:sourcenodes_def)
    from IH[OF all `targetnode ax' -asx'\<rightarrow>* nx`]
    have "\<forall>ni\<in>set (sourcenodes asx'). x \<notin> Def ni" .
    with `\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni`
    have "\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni"
      by(auto simp:sourcenodes_def)
    from `n' -ax'#asx'\<rightarrow>* nx` `nx -as''\<rightarrow>* m` have "n' -(ax'#asx')@as''\<rightarrow>* m" 
      by-(rule path_Append)
    hence "n' -ax'#asx'@as''\<rightarrow>* m" by simp
    have "x \<notin> Def (sourcenode ax')"
    proof
      assume "x \<in> Def (sourcenode ax')"
      with `x \<in> Use m` `\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni`
        `n' -ax'#asx'@as''\<rightarrow>* m` `n' = sourcenode ax'` 
      have "n' influences x in m"
        by(auto simp:data_dependence_def)
      with `m \<in> backward_slice S` dd_closed have "n' \<in> backward_slice S" 
        by(auto simp:dd_closed)
      with `n' = sourcenode ax'` `sourcenode ax' \<notin> backward_slice S`
      show False by simp
    qed
    with `\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni`
    show ?case by(simp add:sourcenodes_def)
  qed
  with `\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni` 
  have "\<forall>ni\<in>set (sourcenodes (asx@as'')). x \<notin> Def ni"
    by(auto simp:sourcenodes_def)
  from `n' -asx\<rightarrow>* nx` `nx -as''\<rightarrow>* m` have "n' -asx@as''\<rightarrow>* m" by(rule path_Append)
  with `m \<in> backward_slice S` `x \<in> Use m` 
    `\<forall>ni\<in>set (sourcenodes (asx@as'')). x \<notin> Def ni` show "x \<in> rv S n'" by -(rule rvI)
qed


lemma closed_eq_obs_eq_rvs:
  fixes S :: "'node set"
  assumes "valid_node n" and "valid_node n'"
  and obs_eq:"obs n (backward_slice S) = obs n' (backward_slice S)"
  shows "rv S n = rv S n'"
proof
  show "rv S n \<subseteq> rv S n'"
  proof
    fix x assume "x \<in> rv S n"
    with `valid_node n` obs_eq show "x \<in> rv S n'" by -(rule eq_obs_in_rv)
  qed
next
  show "rv S n' \<subseteq> rv S n"
  proof
    fix x assume "x \<in> rv S n'"
    with `valid_node n'` obs_eq[THEN sym] show "x \<in> rv S n" by -(rule eq_obs_in_rv)
  qed
qed


lemma rv_edge_slice_kinds:
  assumes "valid_edge a" and "sourcenode a = n" and "targetnode a = n''"
  and "\<forall>V\<in>rv S n. state_val s V = state_val s' V"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (a#asx)) s'"
  shows "\<forall>V\<in>rv S n''. state_val (transfer (slice_kind S a) s) V =
                       state_val (transfer (slice_kind S a) s') V"
proof
  fix V assume "V \<in> rv S n''"
  show "state_val (transfer (slice_kind S a) s) V =
    state_val (transfer (slice_kind S a) s') V"
  proof(cases "V \<in> Def n")
    case True
    show ?thesis
    proof(cases "sourcenode a \<in> backward_slice S")
      case True
      hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
      with `preds (slice_kinds S (a#as)) s` have "pred (kind a) s"
        by(simp add:slice_kinds_def)
      from `slice_kind S a = kind a` `preds (slice_kinds S (a#asx)) s'`
      have "pred (kind a) s'"
        by(simp add:slice_kinds_def)
      from `valid_edge a` `sourcenode a = n` have "n -[]\<rightarrow>* n"
        by(fastforce intro:empty_path)
      with True `sourcenode a = n` have "\<forall>V \<in> Use n. V \<in> rv S n"
        by(fastforce intro:rvI simp:sourcenodes_def)
      with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `sourcenode a = n`
      have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
      from `valid_edge a` this `pred (kind a) s` `pred (kind a) s'`
      have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s) V =
        state_val (transfer (kind a) s') V"
        by(rule CFG_edge_transfer_uses_only_Use)
      with `V \<in> Def n` `sourcenode a = n` `slice_kind S a = kind a`
      show ?thesis by simp
    next
      case False
      from `V \<in> rv S n''` obtain xs nx where "n'' -xs\<rightarrow>* nx"
        and "nx \<in> backward_slice S" and "V \<in> Use nx"
        and "\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'" by(erule rvE)
      from `valid_edge a` `sourcenode a = n` `targetnode a = n''` 
        `n'' -xs\<rightarrow>* nx`
      have "n -a#xs\<rightarrow>* nx" by -(rule path.Cons_path)
      with `V \<in> Def n` `V \<in> Use nx` `\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'`
      have "n influences V in nx" by(fastforce simp:data_dependence_def)
      with `nx \<in> backward_slice S` have "n \<in> backward_slice S"
        by(rule dd_closed)
      with `sourcenode a = n` False have False by simp
      thus ?thesis by simp
    qed
  next
    case False
    from `V \<in> rv S n''` obtain xs nx where "n'' -xs\<rightarrow>* nx"
      and "nx \<in> backward_slice S" and "V \<in> Use nx"
      and "\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'" by(erule rvE)
    from `valid_edge a` `sourcenode a = n` `targetnode a = n''` `n'' -xs\<rightarrow>* nx`
    have "n -a#xs\<rightarrow>* nx" by -(rule path.Cons_path)
    from False `\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'` `sourcenode a = n`
    have "\<forall>nx' \<in> set(sourcenodes (a#xs)). V \<notin> Def nx'"
      by(simp add:sourcenodes_def)
    with `n -a#xs\<rightarrow>* nx` `nx \<in> backward_slice S` `V \<in> Use nx`
    have "V \<in> rv S n" by(rule rvI)
    show ?thesis
    proof(cases "kind a")
      case (Predicate Q)
      show ?thesis
      proof(cases "sourcenode a \<in> backward_slice S")
        case True
        with Predicate have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(simp add:slice_kind_in_slice)
        with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `V \<in> rv S n`
        show ?thesis by simp
      next
        case False
        with Predicate obtain Q' where "slice_kind S a = (Q')\<^sub>\<surd>" 
          by -(erule kind_Predicate_notin_slice_slice_kind_Predicate)
        with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `V \<in> rv S n`
        show ?thesis by simp
      qed
    next
      case (Update f)
      show ?thesis
      proof(cases "sourcenode a \<in> backward_slice S")
        case True
        hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
        from Update have "pred (kind a) s" by simp
        with `valid_edge a` `sourcenode a = n` `V \<notin> Def n`
        have "state_val (transfer (kind a) s) V = state_val s V"
          by(fastforce intro:CFG_edge_no_Def_equal)
        from Update have "pred (kind a) s'" by simp
        with `valid_edge a` `sourcenode a = n` `V \<notin> Def n`
        have "state_val (transfer (kind a) s') V = state_val s' V"
          by(fastforce intro:CFG_edge_no_Def_equal)
        with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `V \<in> rv S n`
          `state_val (transfer (kind a) s) V = state_val s V`
          `slice_kind S a = kind a`
        show ?thesis by fastforce
      next
        case False
        with Update have "slice_kind S a = \<Up>id" by -(rule slice_kind_Upd)
        with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `V \<in> rv S n`
        show ?thesis by fastforce
      qed
    qed
  qed
qed



lemma rv_branching_edges_slice_kinds_False:
  assumes "valid_edge a" and "valid_edge ax" 
  and "sourcenode a = n" and "sourcenode ax = n"
  and "targetnode a = n''" and "targetnode ax \<noteq> n''"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (ax#asx)) s'"
  and "\<forall>V\<in>rv S n. state_val s V = state_val s' V"
  shows False
proof -
  from `valid_edge a` `valid_edge ax` `sourcenode a = n` `sourcenode ax = n`
    `targetnode a = n''` `targetnode ax \<noteq> n''`
  obtain Q Q' where "kind a = (Q)\<^sub>\<surd>" and "kind ax = (Q')\<^sub>\<surd>"
    and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from `valid_edge a` `valid_edge ax` `sourcenode a = n` `sourcenode ax = n`
    `targetnode a = n''` `targetnode ax \<noteq> n''`
  obtain P P' where "slice_kind S a = (P)\<^sub>\<surd>" 
    and "slice_kind S ax = (P')\<^sub>\<surd>"
    and "\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)"
    by -(erule slice_deterministic,auto)
  show ?thesis
  proof(cases "sourcenode a \<in> backward_slice S")
    case True
    hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
    with `preds (slice_kinds S (a#as)) s` `kind a = (Q)\<^sub>\<surd>` 
      `slice_kind S a = (P)\<^sub>\<surd>` have "pred (kind a) s"
      by(simp add:slice_kinds_def)
    from True `sourcenode a = n` `sourcenode ax = n`
    have "slice_kind S ax = kind ax" by(fastforce simp:slice_kind_in_slice)
    with `preds (slice_kinds S (ax#asx)) s'` `kind ax = (Q')\<^sub>\<surd>`
      `slice_kind S ax = (P')\<^sub>\<surd>` have "pred (kind ax) s'" 
      by(simp add:slice_kinds_def)
    with `kind ax = (Q')\<^sub>\<surd>` have "Q' s'" by simp
    from `valid_edge a` `sourcenode a = n` have "n -[]\<rightarrow>* n"
      by(fastforce intro:empty_path)
    with True `sourcenode a = n` have "\<forall>V \<in> Use n. V \<in> rv S n"
      by(fastforce intro:rvI simp:sourcenodes_def)
    with `\<forall>V\<in>rv S n. state_val s V = state_val s' V` `sourcenode a = n`
    have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
    with `valid_edge a` `pred (kind a) s` have "pred (kind a) s'"
      by(rule CFG_edge_Uses_pred_equal)
    with `kind a = (Q)\<^sub>\<surd>` have "Q s'" by simp
    with `Q' s'` `\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)` have False by simp
    thus ?thesis by simp
  next
    case False
    with `kind a = (Q)\<^sub>\<surd>` `slice_kind S a = (P)\<^sub>\<surd>`
    have "P = (\<lambda>s. False) \<or> P = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with `slice_kind S a = (P)\<^sub>\<surd>` `preds (slice_kinds S (a#as)) s`
    have "P = (\<lambda>s. True)" by(fastforce simp:slice_kinds_def)
    from `kind ax = (Q')\<^sub>\<surd>` `slice_kind S ax = (P')\<^sub>\<surd>` 
      `sourcenode a = n` `sourcenode ax = n` False
    have "P' = (\<lambda>s. False) \<or> P' = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with `slice_kind S ax = (P')\<^sub>\<surd>` `preds (slice_kinds S (ax#asx)) s'`
    have "P' = (\<lambda>s. True)" by(fastforce simp:slice_kinds_def)
    with `P = (\<lambda>s. True)` `\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)`
    have False by blast
    thus ?thesis by simp
  qed
qed



subsection {* The set @{text WS} *}

inductive_set WS :: "'node set \<Rightarrow> (('node \<times> 'state) \<times> ('node \<times> 'state)) set"
for S :: "'node set"
where WSI:"\<lbrakk>obs n (backward_slice S) = obs n' (backward_slice S); 
            \<forall>V \<in> rv S n. state_val s V = state_val s' V;
            valid_node n; valid_node n'\<rbrakk>
  \<Longrightarrow> ((n,s),(n',s')) \<in> WS S"


lemma WSD:
  "((n,s),(n',s')) \<in> WS S 
  \<Longrightarrow> obs n (backward_slice S) = obs n' (backward_slice S) \<and> 
      (\<forall>V \<in> rv S n. state_val s V = state_val s' V) \<and>
      valid_node n \<and> valid_node n'"
by(auto elim:WS.cases)


lemma WS_silent_move:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1')"
  and "obs n\<^sub>1' (backward_slice S) \<noteq> {}" shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
proof -
  from `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` have "valid_node n\<^sub>1" and "valid_node n\<^sub>2"
    by(auto dest:WSD)
  from `S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1')` have "sourcenode a = n\<^sub>1"
    and "targetnode a = n\<^sub>1'" and "transfer (kind a) s\<^sub>1 = s\<^sub>1'"
    and "n\<^sub>1 \<notin> backward_slice S" and "valid_edge a" and "pred (kind a) s\<^sub>1"
    by(auto elim:silent_move.cases)
  from `targetnode a = n\<^sub>1'` `valid_edge a` have "valid_node n\<^sub>1'"
    by(auto simp:valid_node_def)
  have "(\<exists>m. obs n\<^sub>1' (backward_slice S) = {m}) \<or> obs n\<^sub>1' (backward_slice S) = {}"
    by(rule obs_singleton_disj)
  with `obs n\<^sub>1' (backward_slice S) \<noteq> {}` obtain n 
    where "obs n\<^sub>1' (backward_slice S) = {n}" by fastforce
  hence "n \<in> obs n\<^sub>1' (backward_slice S)" by auto
  then obtain as where "n\<^sub>1' -as\<rightarrow>* n" 
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)" 
    and "n \<in> (backward_slice S)" by(erule obsE)
  from `n\<^sub>1' -as\<rightarrow>* n` `valid_edge a` `sourcenode a = n\<^sub>1` `targetnode a = n\<^sub>1'`
  have "n\<^sub>1 -a#as\<rightarrow>* n" by(rule Cons_path)
  moreover
  from `\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)` `sourcenode a = n\<^sub>1`
    `n\<^sub>1 \<notin> backward_slice S` 
  have "\<forall>nx \<in> set(sourcenodes (a#as)). nx \<notin> (backward_slice S)"
    by(simp add:sourcenodes_def)
  ultimately have "n \<in> obs n\<^sub>1 (backward_slice S)" using `n \<in> (backward_slice S)` 
    by(rule obs_elem)
  hence "obs n\<^sub>1 (backward_slice S) = {n}" by(rule obs_singleton_element)
  with `obs n\<^sub>1' (backward_slice S) = {n}` 
  have "obs n\<^sub>1 (backward_slice S) = obs n\<^sub>1' (backward_slice S)"
    by simp
  with `valid_node n\<^sub>1` `valid_node n\<^sub>1'` have "rv S n\<^sub>1 = rv S n\<^sub>1'"
    by(rule closed_eq_obs_eq_rvs)
  from `n \<in> obs n\<^sub>1 (backward_slice S)` `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` 
  have "obs n\<^sub>1 (backward_slice S) = obs n\<^sub>2 (backward_slice S)"
    and "\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V"
    by(fastforce dest:WSD)+
  from `obs n\<^sub>1 (backward_slice S) = obs n\<^sub>2 (backward_slice S)`
    `obs n\<^sub>1 (backward_slice S) = {n}` `obs n\<^sub>1' (backward_slice S) = {n}` 
  have "obs n\<^sub>1' (backward_slice S) = obs n\<^sub>2 (backward_slice S)" by simp
  have "\<forall>V \<in> rv S n\<^sub>1'. state_val s\<^sub>1' V = state_val s\<^sub>2 V"
  proof
    fix V assume "V \<in> rv S n\<^sub>1'"
    with `rv S n\<^sub>1 = rv S n\<^sub>1'` have "V \<in> rv S n\<^sub>1" by simp
    then obtain as n' where "n\<^sub>1 -as\<rightarrow>* n'" and "n' \<in> (backward_slice S)"
      and "V \<in> Use n'" and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx"
      by(erule rvE)
    with `n\<^sub>1 \<notin> backward_slice S` have "V \<notin> Def n\<^sub>1"
      by(auto elim:path.cases simp:sourcenodes_def)
    with `valid_edge a` `sourcenode a = n\<^sub>1` `pred (kind a) s\<^sub>1`
    have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
      by(fastforce intro:CFG_edge_no_Def_equal)
    with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "state_val s\<^sub>1' V = state_val s\<^sub>1 V" by simp
    from `V \<in> rv S n\<^sub>1` `\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V`
    have "state_val s\<^sub>1 V = state_val s\<^sub>2 V" by simp
    with `state_val s\<^sub>1' V = state_val s\<^sub>1 V` 
    show "state_val s\<^sub>1' V = state_val s\<^sub>2 V" by simp
  qed
  with `obs n\<^sub>1' (backward_slice S) = obs n\<^sub>2 (backward_slice S)`
    `valid_node n\<^sub>1'` `valid_node n\<^sub>2` show ?thesis by(fastforce intro:WSI)
qed


lemma WS_silent_moves:
  "\<lbrakk>S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1'); ((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S; f = kind;
    obs n\<^sub>1' (backward_slice S) \<noteq> {}\<rbrakk>
  \<Longrightarrow> ((n\<^sub>1',s\<^sub>1'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  note IH = `\<lbrakk>((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S; f = kind; obs n'' (backward_slice S) \<noteq> {}\<rbrakk>
             \<Longrightarrow> ((n'',s''),(n\<^sub>2,s\<^sub>2)) \<in> WS S`
  from `S,f \<turnstile> (n',s') =as\<Rightarrow>\<^sub>\<tau> (n'',s'')` `obs n'' (backward_slice S) \<noteq> {}`
  have "obs n' (backward_slice S) \<noteq> {}" by(fastforce dest:silent_moves_obs_slice)
  with `((n,s),(n\<^sub>2,s\<^sub>2)) \<in> WS S` `S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')` `f = kind`
  have "((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S" by -(rule WS_silent_move,simp+)
  from IH[OF this `f = kind` `obs n'' (backward_slice S) \<noteq> {}`]
  show ?case .
qed



lemma WS_observable_move:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow> (n\<^sub>1',s\<^sub>1')"
  obtains as where "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
proof(atomize_elim)
  from `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` have "valid_node n\<^sub>1" by(auto dest:WSD)
  from `S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow> (n\<^sub>1',s\<^sub>1')` have [simp]:"n\<^sub>1 = sourcenode a" 
    and [simp]:"n\<^sub>1' = targetnode a" and "pred (kind a) s\<^sub>1"
    and "transfer (kind a) s\<^sub>1 = s\<^sub>1'" and "n\<^sub>1 \<in> (backward_slice S)" 
    and "valid_edge a" and "pred (kind a) s\<^sub>1"
    by(auto elim:observable_move.cases)
  from  `valid_edge a` have "valid_node n\<^sub>1'" by(auto simp:valid_node_def)
  from `valid_node n\<^sub>1` `n\<^sub>1 \<in> (backward_slice S)` 
  have "obs n\<^sub>1 (backward_slice S) = {n\<^sub>1}" by(rule n_in_obs)
  with `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` have "obs n\<^sub>2 (backward_slice S) = {n\<^sub>1}" 
    and "\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V" by(auto dest:WSD)
  from `valid_node n\<^sub>1` have "n\<^sub>1 -[]\<rightarrow>* n\<^sub>1" by(rule empty_path)
  with `n\<^sub>1 \<in> (backward_slice S)` have "\<forall>V \<in> Use n\<^sub>1. V \<in> rv S n\<^sub>1"
    by(fastforce intro:rvI simp:sourcenodes_def)
  with `\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V`
  have "\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V" by blast
  with `valid_edge a`  `pred (kind a) s\<^sub>1` have "pred (kind a) s\<^sub>2"
    by(fastforce intro:CFG_edge_Uses_pred_equal)
  with `n\<^sub>1 \<in> (backward_slice S)` have "pred (slice_kind S a) s\<^sub>2"
    by(simp add:slice_kind_in_slice)
  from `n\<^sub>1 \<in> (backward_slice S)` obtain s\<^sub>2' 
    where "transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'"
    by(simp add:slice_kind_in_slice)
  with `pred (slice_kind S a) s\<^sub>2` `n\<^sub>1 \<in> (backward_slice S)` `valid_edge a` 
  have "S,slice_kind S \<turnstile> (n\<^sub>1,s\<^sub>2) -a\<rightarrow> (n\<^sub>1',s\<^sub>2')"
    by(fastforce intro:observable_moveI)
  from `obs n\<^sub>2 (backward_slice S) = {n\<^sub>1}`
  obtain as where "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (n\<^sub>1,s\<^sub>2)"
    by(erule obs_silent_moves)
  with `S,slice_kind S \<turnstile> (n\<^sub>1,s\<^sub>2) -a\<rightarrow> (n\<^sub>1',s\<^sub>2')` 
  have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',s\<^sub>2')"
    by -(rule observable_moves_snoc)
  have "\<forall>V \<in> rv S n\<^sub>1'. state_val s\<^sub>1' V = state_val s\<^sub>2' V"
  proof
    fix V assume rv:"V \<in> rv S n\<^sub>1'"
    show "state_val s\<^sub>1' V = state_val s\<^sub>2' V"
    proof(cases "V \<in> Def n\<^sub>1")
      case True
      thus ?thesis
      proof(cases "kind a")
        case (Update f)
        with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "s\<^sub>1' = f s\<^sub>1" by simp
        from Update[THEN sym] `n\<^sub>1 \<in> (backward_slice S)` 
        have "slice_kind S a = \<Up>f"
          by(fastforce intro:slice_kind_in_slice)
        with `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'` have "s\<^sub>2' = f s\<^sub>2" by simp
        from `valid_edge a` `\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V`
          True Update `s\<^sub>1' = f s\<^sub>1` `s\<^sub>2' = f s\<^sub>2` show ?thesis
          by(fastforce dest:CFG_edge_transfer_uses_only_Use)
      next
        case (Predicate Q)
        with `transfer (kind a) s\<^sub>1 = s\<^sub>1'` have "s\<^sub>1' = s\<^sub>1" by simp
        from Predicate[THEN sym] `n\<^sub>1 \<in> (backward_slice S)`
        have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(fastforce intro:slice_kind_in_slice)
        with `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'` have "s\<^sub>2' = s\<^sub>2" by simp
        with `valid_edge a` `\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V` 
          True Predicate `s\<^sub>1' = s\<^sub>1` `pred (kind a) s\<^sub>1` `pred (kind a) s\<^sub>2`
        show ?thesis by(auto dest:CFG_edge_transfer_uses_only_Use)
      qed
    next
      case False
      with `valid_edge a` `transfer (kind a) s\<^sub>1 = s\<^sub>1'`[THEN sym] 
        `pred (kind a) s\<^sub>1` `pred (kind a) s\<^sub>2`
      have "state_val s\<^sub>1' V = state_val s\<^sub>1 V"
        by(fastforce intro:CFG_edge_no_Def_equal)
      have "state_val s\<^sub>2' V = state_val s\<^sub>2 V"
      proof(cases "kind a")
        case (Update f)
        with  `n\<^sub>1 \<in> (backward_slice S)` have "slice_kind S a = kind a"
          by(fastforce intro:slice_kind_in_slice)
        with `valid_edge a` `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'`[THEN sym] 
          False `pred (kind a) s\<^sub>2`
        show ?thesis by(fastforce intro:CFG_edge_no_Def_equal)
      next
        case (Predicate Q)
        with `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'` have "s\<^sub>2 = s\<^sub>2'"
          by(cases "slice_kind S a",
            auto split:split_if_asm simp:slice_kind_def Let_def)
        thus ?thesis by simp
      qed
      from rv obtain as' nx where "n\<^sub>1' -as'\<rightarrow>* nx" 
        and "nx \<in> (backward_slice S)"
        and "V \<in> Use nx" and "\<forall>nx \<in> set(sourcenodes as'). V \<notin> Def nx"
        by(erule rvE)
      from `\<forall>nx \<in> set(sourcenodes as'). V \<notin> Def nx` False
      have "\<forall>nx \<in> set(sourcenodes (a#as')). V \<notin> Def nx"
        by(auto simp:sourcenodes_def)
      from  `valid_edge a` `n\<^sub>1' -as'\<rightarrow>* nx` have "n\<^sub>1 -a#as'\<rightarrow>* nx"
        by(fastforce intro:Cons_path)
      with `nx \<in> (backward_slice S)` `V \<in> Use nx` 
        `\<forall>nx \<in> set(sourcenodes (a#as')). V \<notin> Def nx`
      have "V \<in> rv S n\<^sub>1" by -(rule rvI)
      with `\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V` 
        `state_val s\<^sub>1' V = state_val s\<^sub>1 V` `state_val s\<^sub>2' V = state_val s\<^sub>2 V`
      show ?thesis by fastforce
    qed
  qed
  with `valid_node n\<^sub>1'` have "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',s\<^sub>2')) \<in> WS S" by(fastforce intro:WSI)
  with `S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',s\<^sub>2')`
    `transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'` 
  show "\<exists>as. ((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
    by blast
qed



definition is_weak_sim :: 
  "(('node \<times> 'state) \<times> ('node \<times> 'state)) set \<Rightarrow> 'node set \<Rightarrow> bool"
  where "is_weak_sim R S \<equiv> 
  \<forall>n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 n\<^sub>1' s\<^sub>1' as. ((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> R \<and> S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')
  \<longrightarrow> (\<exists>n\<^sub>2' s\<^sub>2' as'. ((n\<^sub>1',s\<^sub>1'),(n\<^sub>2',s\<^sub>2')) \<in> R \<and> 
                      S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'\<Rightarrow> (n\<^sub>2',s\<^sub>2'))"


lemma WS_weak_sim:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" 
  and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')"
  shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
  (\<exists>as'. S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
                             (n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2))"
proof -
  from `S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')` obtain a' as' n' s'
    where "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (n',s')" 
    and "S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')" and "as = as'@[a']"
    by(fastforce elim:observable_moves.cases)
  from `S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')` have "obs n' (backward_slice S) = {n'}"
    by(fastforce elim:observable_move.cases intro!:n_in_obs)
  hence "obs n' (backward_slice S) \<noteq> {}" by fast
  with `S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (n',s')` `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` 
  have "((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
    by -(rule WS_silent_moves,simp+)
  with `S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')` obtain asx 
    where "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S"
    and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx@[a']\<Rightarrow> 
    (n\<^sub>1',transfer (slice_kind S a') s\<^sub>2)"
    by(fastforce elim:WS_observable_move)
  with `as = as'@[a']` show
    "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
    (\<exists>as'. S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
           (n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2))" by simp blast
qed

text {* The following lemma states the correctness of static intraprocedural slicing:\\
  the simulation @{text "WS S"} is a desired weak simulation *}

theorem WS_is_weak_sim:"is_weak_sim (WS S) S"
by(fastforce dest:WS_weak_sim simp:is_weak_sim_def)


subsection {* @{term "n -as\<rightarrow>* n'"} and transitive closure of 
  @{term "S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')"} *}

inductive trans_observable_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow>* '(_,_')" [51,50,0,0,50,0,0] 51) 

where tom_Nil:
  "S,f \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)"

| tom_Cons:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s'); S,f \<turnstile> (n',s') =as'\<Rightarrow>* (n'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (n,s) =(last as)#as'\<Rightarrow>* (n'',s'')"


definition slice_edges :: "'node set \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "slice_edges S as \<equiv> [a \<leftarrow> as. sourcenode a \<in> backward_slice S]"


lemma silent_moves_no_slice_edges:
  "S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s') \<Longrightarrow> slice_edges S as = []"
by(induct rule:silent_moves.induct,auto elim:silent_move.cases simp:slice_edges_def)


lemma observable_moves_last_slice_edges:
  "S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s') \<Longrightarrow> slice_edges S as = [last as]"
by(induct rule:observable_moves.induct,
   fastforce dest:silent_moves_no_slice_edges elim:observable_move.cases 
            simp:slice_edges_def)


lemma slice_edges_no_nodes_in_slice:
  "slice_edges S as = [] 
  \<Longrightarrow> \<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
proof(induct as)
  case Nil thus ?case by(simp add:slice_edges_def sourcenodes_def)
next
  case (Cons a' as')
  note IH = `slice_edges S as' = [] \<Longrightarrow>
    \<forall>nx\<in>set (sourcenodes as'). nx \<notin> backward_slice S`
  from `slice_edges S (a'#as') = []` have "slice_edges S as' = []"
    and "sourcenode a' \<notin> backward_slice S"
    by(auto simp:slice_edges_def split:split_if_asm)
  from IH[OF `slice_edges S as' = []`] `sourcenode a' \<notin> backward_slice S`
  show ?case by(simp add:sourcenodes_def)
qed



lemma sliced_path_determ:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as'\<rightarrow>* n'; slice_edges S as = slice_edges S as';
    preds (slice_kinds S as) s; preds (slice_kinds S as') s'; n' \<in> S;
    \<forall>V \<in> rv S n. state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> as = as'"
proof(induct arbitrary:as' s s' rule:path.induct)
  case (empty_path n)
  from `slice_edges S [] = slice_edges S as'` 
  have "\<forall>nx \<in> set(sourcenodes as'). nx \<notin> (backward_slice S)"
    by(fastforce intro!:slice_edges_no_nodes_in_slice simp:slice_edges_def)
  with `n -as'\<rightarrow>* n` show ?case
  proof(induct nx\<equiv>"n" as' nx'\<equiv>"n" rule:path.induct)
    case (Cons_path n'' as a)
    from `valid_node n` `n \<in> S` have "n \<in> backward_slice S" by(rule refl)
    with `\<forall>nx\<in>set (sourcenodes (a # as)). nx \<notin> backward_slice S` 
      `sourcenode a = n`
    have False by(simp add:sourcenodes_def)
    thus ?case by simp
  qed simp
next
  case (Cons_path n'' as n' a n)
  note IH = `\<And>as' s s'. \<lbrakk>n'' -as'\<rightarrow>* n'; slice_edges S as = slice_edges S as';
    preds (slice_kinds S as) s; preds (slice_kinds S as') s'; n' \<in> S;
    \<forall>V\<in>rv S n''. state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> as = as'`
  show ?case
  proof(cases as')
    case Nil
    with `n -as'\<rightarrow>* n'` have "n = n'" by fastforce
    from Nil `slice_edges S (a#as) = slice_edges S as'` `sourcenode a = n`
    have "n \<notin> backward_slice S" by(fastforce simp:slice_edges_def)
    from `valid_edge a` `sourcenode a = n` `n = n'` `n' \<in> S`
    have "n \<in> backward_slice S" by(fastforce intro:refl)
    with `n = n'` `n \<notin> backward_slice S` have False by simp
    thus ?thesis by simp
  next
    case (Cons ax asx)
    with `n -as'\<rightarrow>* n'` have "n = sourcenode ax" and "valid_edge ax" 
      and "targetnode ax -asx\<rightarrow>* n'" by(auto elim:path_split_Cons)
    show ?thesis
    proof(cases "targetnode ax = n''")
      case True
      with `targetnode ax -asx\<rightarrow>* n'` have "n'' -asx\<rightarrow>* n'" by simp
      from `valid_edge ax` `valid_edge a` `n = sourcenode ax` `sourcenode a = n`
        True `targetnode a = n''` have "ax = a" by(fastforce intro:edge_det)
      from `slice_edges S (a#as) = slice_edges S as'` Cons 
        `n = sourcenode ax` `sourcenode a = n`
      have "slice_edges S as = slice_edges S asx"
        by(cases "n \<in> backward_slice S")(auto simp:slice_edges_def)
      from `preds (slice_kinds S (a#as)) s` 
      have preds1:"preds (slice_kinds S as) (transfer (slice_kind S a) s)"
        by(simp add:slice_kinds_def)
      from `preds (slice_kinds S as') s'` Cons `ax = a`
      have preds2:"preds (slice_kinds S asx) (transfer (slice_kind S a) s')"
        by(simp add:slice_kinds_def)
      from `valid_edge a` `sourcenode a = n` `targetnode a = n''`
        `preds (slice_kinds S (a#as)) s` `preds (slice_kinds S as') s'`
        `ax = a` Cons `\<forall>V\<in>rv S n. state_val s V = state_val s' V`
      have "\<forall>V\<in>rv S n''. state_val (transfer (slice_kind S a) s) V =
                          state_val (transfer (slice_kind S a) s') V"
        by -(rule rv_edge_slice_kinds,auto)
      from IH[OF `n'' -asx\<rightarrow>* n'` `slice_edges S as = slice_edges S asx`
        preds1 preds2 `n' \<in> S` this] Cons `ax = a` show ?thesis by simp
    next
      case False
      with `valid_edge a` `valid_edge ax` `sourcenode a = n` `n = sourcenode ax`
        `targetnode a = n''` `preds (slice_kinds S (a#as)) s`
        `preds (slice_kinds S as') s'` Cons
        `\<forall>V\<in>rv S n. state_val s V = state_val s' V`
      have False by -(erule rv_branching_edges_slice_kinds_False,auto)
      thus ?thesis by simp
    qed
  qed
qed



lemma path_trans_observable_moves:
  assumes "n -as\<rightarrow>* n'" and "preds (kinds as) s" and "transfers (kinds as) s = s'"
  obtains n'' s'' as' as'' where "S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')"
  and "S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s')" 
  and "slice_edges S as = slice_edges S as''" and "n -as''@as'\<rightarrow>* n'"
proof(atomize_elim)
  from `n -as\<rightarrow>* n'` `preds (kinds as) s` `transfers (kinds as) s = s'`
  show "\<exists>n'' s'' as' as''. 
    S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'') \<and>
    S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s') \<and> slice_edges S as = slice_edges S as'' \<and>
    n -as''@as'\<rightarrow>* n'"
  proof(induct arbitrary:s rule:path.induct)
    case (empty_path n)
    from `transfers (kinds []) s = s'` have "s = s'" by(simp add:kinds_def)
    have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)" by(rule tom_Nil)
    have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n,s)" by(rule silent_moves_Nil)
    with `S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)` `s = s'` `valid_node n`
    show ?case
      apply(rule_tac x="n" in exI)
      apply(rule_tac x="s" in exI)
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="[]" in exI)
      by(fastforce intro:path.empty_path simp:slice_edges_def)
  next
    case (Cons_path n'' as n' a n)
    note IH = `\<And>s. \<lbrakk>preds (kinds as) s; transfers (kinds as) s = s'\<rbrakk>
      \<Longrightarrow> \<exists>nx s'' as' as''. S,kind \<turnstile> (n'',s) =slice_edges S as\<Rightarrow>* (nx,s'') \<and>
            S,kind \<turnstile> (nx,s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s') \<and> 
            slice_edges S as = slice_edges S as'' \<and> n'' -as''@as'\<rightarrow>* n'`
    from `preds (kinds (a#as)) s` `transfers (kinds (a#as)) s = s'`
    have "preds (kinds as) (transfer (kind a) s)" 
      "transfers (kinds as) (transfer (kind a) s) = s'" by(simp_all add:kinds_def)
    from IH[OF this] obtain nx sx asx asx'
      where "S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)"
      and "S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')"
      and "slice_edges S as = slice_edges S asx'"
      and "n'' -asx'@asx\<rightarrow>* n'"
      by clarsimp
    from `preds (kinds (a#as)) s` have "pred (kind a) s" by(simp add:kinds_def)
    show ?case
    proof(cases "n \<in> backward_slice S")
      case True
      with `valid_edge a` `sourcenode a = n` `targetnode a = n''` `pred (kind a) s`
      have "S,kind \<turnstile> (n,s) -a\<rightarrow> (n'',transfer (kind a) s)"
        by(fastforce intro:observable_moveI)
      hence "S,kind \<turnstile> (n,s) =[]@[a]\<Rightarrow> (n'',transfer (kind a) s)"
        by(fastforce intro:observable_moves_snoc silent_moves_Nil)
      with `S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)`
      have "S,kind \<turnstile> (n,s) =a#slice_edges S as\<Rightarrow>* (nx,sx)"
        by(fastforce dest:tom_Cons)
      with `S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')`
        `slice_edges S as = slice_edges S asx'` `n'' -asx'@asx\<rightarrow>* n'`
        `sourcenode a = n` `valid_edge a` `targetnode a = n''` True
      show ?thesis
        apply(rule_tac x="nx" in exI)
        apply(rule_tac x="sx" in exI)
        apply(rule_tac x="asx" in exI)
        apply(rule_tac x="a#asx'" in exI)
        by(auto intro:path.Cons_path simp:slice_edges_def)
    next
      case False
      with `valid_edge a` `sourcenode a = n` `targetnode a = n''` `pred (kind a) s`
      have "S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',transfer (kind a) s)"
        by(fastforce intro:silent_moveI)
      from `S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)`
      obtain f s'' asx'' where "S,f \<turnstile> (n'',s'') =asx''\<Rightarrow>* (nx,sx)"
        and "f = kind" and "s'' = transfer (kind a) s" 
        and "asx'' = slice_edges S as" by simp
      from `S,f \<turnstile> (n'',s'') =asx''\<Rightarrow>* (nx,sx)` `f = kind`
        `asx'' = slice_edges S as` `s'' = transfer (kind a) s`
        `S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',transfer (kind a) s)` 
        `S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')` `slice_edges S as = slice_edges S asx'`
        `n'' -asx'@asx\<rightarrow>* n'` False
      show ?thesis
      proof(induct rule:trans_observable_moves.induct)
        case (tom_Nil S f ni si)
        have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)" by(rule trans_observable_moves.tom_Nil)
        from `S,kind \<turnstile> (ni,si) =asx\<Rightarrow>\<^sub>\<tau> (n',s')`
          `S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)` 
          `si = transfer (kind a) s`
        have "S,kind \<turnstile> (n,s) =a#asx\<Rightarrow>\<^sub>\<tau> (n',s')"
          by(fastforce intro:silent_moves_Cons)
        with `valid_edge a` `sourcenode a = n`
        have "n -a#asx\<rightarrow>* n'" by(fastforce dest:silent_moves_preds_transfers_path)
        with `sourcenode a = n` `valid_edge a` `targetnode a = n''`
          `[] = slice_edges S as` `n \<notin> backward_slice S`
          `S,kind \<turnstile> (n,s) =a#asx\<Rightarrow>\<^sub>\<tau> (n',s')`
        show ?case
          apply(rule_tac x="n" in exI)
          apply(rule_tac x="s" in exI)
          apply(rule_tac x="a#asx" in exI)
          apply(rule_tac x="[]" in exI)
          by(fastforce simp:slice_edges_def intro:trans_observable_moves.tom_Nil)
      next
        case (tom_Cons S f ni si asi ni' si' asi' n'' s'')
        from `S,f \<turnstile> (ni,si) =asi\<Rightarrow> (ni',si')` have "asi \<noteq> []"
          by(fastforce dest:observable_move_notempty)
        from `S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)`
        have "valid_edge a" and "sourcenode a = n" and "targetnode a = ni"
          by(auto elim:silent_move.cases)
        from `S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)` `f = kind`
          `si = transfer (kind a) s` `S,f \<turnstile> (ni,si) =asi\<Rightarrow> (ni',si')`
        have "S,f \<turnstile> (n,s) =a#asi\<Rightarrow> (ni',si')"
          by(fastforce intro:silent_move_observable_moves)
        with `S,f \<turnstile> (ni',si') =asi'\<Rightarrow>* (n'',s'')`
        have "S,f \<turnstile> (n,s) =(last (a#asi))#asi'\<Rightarrow>* (n'',s'')"
          by -(rule trans_observable_moves.tom_Cons)
        with `f = kind` `last asi # asi' = slice_edges S as` `n \<notin> backward_slice S`
          `S,kind \<turnstile> (n'',s'') =asx\<Rightarrow>\<^sub>\<tau> (n',s')`  `sourcenode a = n` `asi \<noteq> []`
          `ni -asx'@asx\<rightarrow>* n'` `slice_edges S as = slice_edges S asx'`
          `valid_edge a` `sourcenode a = n` `targetnode a = ni`
        show ?case
          apply(rule_tac x="n''" in exI)
          apply(rule_tac x="s''" in exI)
          apply(rule_tac x="asx" in exI)
          apply(rule_tac x="a#asx'" in exI)
          by(auto intro:path.Cons_path simp:slice_edges_def)
      qed
    qed
  qed
qed


lemma WS_weak_sim_trans:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
  and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')" and "as \<noteq> []"
  shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)) \<in> WS S \<and> 
         S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>* (n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)"
proof -
  obtain f where "f = kind" by simp
  with `S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')` 
  have "S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')" by simp
  from `S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')` `((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S` `as \<noteq> []` `f = kind`
  show "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>* (n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)"
  proof(induct arbitrary:n\<^sub>2 s\<^sub>2 rule:trans_observable_moves.induct)
    case tom_Nil thus ?case by simp
  next
    case (tom_Cons S f n s as n' s' as' n'' s'')
    note IH = `\<And>n\<^sub>2 s\<^sub>2. \<lbrakk>((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S; as' \<noteq> []; f = kind\<rbrakk>
      \<Longrightarrow> ((n'',s''),(n'',transfers (slice_kinds S as') s\<^sub>2)) \<in> WS S \<and>
      S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'\<Rightarrow>* (n'',transfers (slice_kinds S as') s\<^sub>2)`
    from `S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')`
    obtain asx ax nx sx where "S,f \<turnstile> (n,s) =asx\<Rightarrow>\<^sub>\<tau> (nx,sx)"
      and "S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')" and "as = asx@[ax]"
      by(fastforce elim:observable_moves.cases)
    from `S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')` have "obs nx (backward_slice S) = {nx}"
      by(fastforce intro!:n_in_obs elim:observable_move.cases)
    with `S,f \<turnstile> (n,s) =asx\<Rightarrow>\<^sub>\<tau> (nx,sx)` `((n,s),(n\<^sub>2,s\<^sub>2)) \<in> WS S` `f = kind`
    have "((nx,sx),(n\<^sub>2,s\<^sub>2)) \<in> WS S" by(fastforce intro:WS_silent_moves)
    with `S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')` `f = kind`
    obtain asx' where "((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S"
      and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
      (n',transfer (slice_kind S ax) s\<^sub>2)"
      by(fastforce elim:WS_observable_move)
    show ?case
    proof(cases "as' = []")
      case True
      with `S,f \<turnstile> (n',s') =as'\<Rightarrow>* (n'',s'')` have "n' = n'' \<and> s' = s''"
        by(fastforce elim:trans_observable_moves.cases dest:observable_move_notempty)
      from `S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
                               (n',transfer (slice_kind S ax) s\<^sub>2)`
      have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =(last (asx'@[ax]))#[]\<Rightarrow>* 
                               (n',transfer (slice_kind S ax) s\<^sub>2)"
        by(fastforce intro:trans_observable_moves.intros)
      with `((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S` `as = asx@[ax]`
        `n' = n'' \<and> s' = s''` True
      show ?thesis by(fastforce simp:slice_kinds_def)
    next
      case False
      from IH[OF `((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S` this 
        `f = kind`]
      have "((n'',s''),(n'',transfers (slice_kinds S as') 
        (transfer (slice_kind S ax) s\<^sub>2))) \<in> WS S"
        and "S,slice_kind S \<turnstile> (n',transfer (slice_kind S ax) s\<^sub>2) 
        =as'\<Rightarrow>* (n'',transfers (slice_kinds S as')
                     (transfer (slice_kind S ax) s\<^sub>2))" by simp_all
      with `S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
                               (n',transfer (slice_kind S ax) s\<^sub>2)`
      have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =(last (asx'@[ax]))#as'\<Rightarrow>* 
        (n'',transfers (slice_kinds S as') (transfer (slice_kind S ax) s\<^sub>2))"
        by(fastforce intro:trans_observable_moves.tom_Cons)
      with `((n'',s''),(n'',transfers (slice_kinds S as') 
        (transfer (slice_kind S ax) s\<^sub>2))) \<in> WS S` False `as = asx@[ax]`
      show ?thesis by(fastforce simp:slice_kinds_def)
    qed
  qed
qed


lemma transfers_slice_kinds_slice_edges:
  "transfers (slice_kinds S (slice_edges S as)) s = transfers (slice_kinds S as) s"
proof(induct as arbitrary:s)
  case Nil thus ?case by(simp add:slice_kinds_def slice_edges_def)
next
  case (Cons a' as')
  note IH = `\<And>s. transfers (slice_kinds S (slice_edges S as')) s =
                  transfers (slice_kinds S as') s`
  show ?case
  proof(cases "sourcenode a' \<in> backward_slice S")
    case True
    hence eq:"transfers (slice_kinds S (slice_edges S (a'#as'))) s
            = transfers (slice_kinds S (slice_edges S as')) 
                (transfer (slice_kind S a') s)"
      by(simp add:slice_edges_def slice_kinds_def)
    have "transfers (slice_kinds S (a'#as')) s
        = transfers (slice_kinds S as') (transfer (slice_kind S a') s)"
      by(simp add:slice_kinds_def)
    with eq IH[of "transfer (slice_kind S a') s"] show ?thesis by simp
  next
    case False
    hence eq:"transfers (slice_kinds S (slice_edges S (a'#as'))) s
            = transfers (slice_kinds S (slice_edges S as')) s"
      by(simp add:slice_edges_def slice_kinds_def)
    from False have "transfer (slice_kind S a') s = s"
      by(cases "kind a'",auto simp:slice_kind_def Let_def)
    hence "transfers (slice_kinds S (a'#as')) s
         = transfers (slice_kinds S as') s"
      by(simp add:slice_kinds_def)
    with eq IH[of s] show ?thesis by simp
  qed
qed


lemma trans_observable_moves_preds:
  assumes "S,f \<turnstile> (n,s) =as\<Rightarrow>* (n',s')" and "valid_node n"
  obtains as' where "preds (map f as') s" and "slice_edges S as' = as"
  and "n -as'\<rightarrow>* n'"
proof(atomize_elim)
  from `S,f \<turnstile> (n,s) =as\<Rightarrow>* (n',s')` `valid_node n`
  show "\<exists>as'. preds (map f as') s \<and> slice_edges S as' = as \<and> n -as'\<rightarrow>* n'"
  proof(induct rule:trans_observable_moves.induct)
    case tom_Nil thus ?case 
      by(rule_tac x="[]" in exI,fastforce intro:empty_path simp:slice_edges_def)
  next
    case (tom_Cons S f n s as n' s' as' n'' s'')
    note IH = `valid_node n' 
      \<Longrightarrow> \<exists>asx. preds (map f asx) s' \<and> slice_edges S asx = as' \<and> n' -asx\<rightarrow>* n''`
    from `S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')`
    have "preds (map f as) s" and "transfers (map f as) s = s'"
      and "n -as\<rightarrow>* n'"
      by(fastforce dest:observable_moves_preds_transfers_path)+
    from `n -as\<rightarrow>* n'` have "valid_node n'" by(fastforce dest:path_valid_node)
    from `S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')` have "slice_edges S as = [last as]"
      by(rule observable_moves_last_slice_edges)
    from IH[OF `valid_node n'`]
    obtain asx where "preds (map f asx) s'" and "slice_edges S asx = as'"
      and "n' -asx\<rightarrow>* n''"
      by blast
    from `n -as\<rightarrow>* n'` `n' -asx\<rightarrow>* n''` have "n -as@asx\<rightarrow>* n''" by(rule path_Append)
    from `preds (map f asx) s'` `transfers (map f as) s = s'`[THEN sym]
      `preds (map f as) s`
    have "preds (map f (as@asx)) s" by(simp add:preds_split)
    with `slice_edges S as = [last as]` `slice_edges S asx = as'` 
      `n -as@asx\<rightarrow>* n''` show ?case
      by(rule_tac x="as@asx" in exI,auto simp:slice_edges_def)
  qed
qed



lemma exists_sliced_path_preds:
  assumes "n -as\<rightarrow>* n'" and "slice_edges S as = []" and "n' \<in> backward_slice S"
  obtains as' where "n -as'\<rightarrow>* n'" and "preds (slice_kinds S as') s"
  and "slice_edges S as' = []"
proof(atomize_elim)
  from `slice_edges S as = []`
  have "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
    by(rule slice_edges_no_nodes_in_slice)
  with `n -as\<rightarrow>* n'` `n' \<in> backward_slice S` have "n' \<in> obs n (backward_slice S)"
    by -(rule obs_elem)
  hence "obs n (backward_slice S) = {n'}" by(rule obs_singleton_element)
  from `n -as\<rightarrow>* n'` have "valid_node n" and "valid_node n'"
    by(fastforce dest:path_valid_node)+
  from `n -as\<rightarrow>* n'` obtain x where "distance n n' x" and "x \<le> length as"
    by(erule every_path_distance)
  from `distance n n' x` `obs n (backward_slice S) = {n'}`
  show "\<exists>as'. n -as'\<rightarrow>* n' \<and> preds (slice_kinds S as') s \<and> 
              slice_edges S as' = []"
  proof(induct x arbitrary:n rule:nat.induct)
    case zero
    from `distance n n' 0` have "n = n'" by(fastforce elim:distance.cases)
    with `valid_node n'` show ?case
      by(rule_tac x="[]" in exI,
        auto intro:empty_path simp:slice_kinds_def slice_edges_def)
  next
    case (Suc x)
    note IH = `\<And>n. \<lbrakk>distance n n' x; obs n (backward_slice S) = {n'}\<rbrakk>
      \<Longrightarrow> \<exists>as'. n -as'\<rightarrow>* n' \<and> preds (slice_kinds S as') s \<and> 
               slice_edges S as' = []`
    from `distance n n' (Suc x)` obtain a 
      where "valid_edge a" and "n = sourcenode a" 
      and "distance (targetnode a) n' x"
      and target:"targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
      distance (targetnode a') n' x \<and>
      valid_edge a' \<and> targetnode a' = nx)"
      by(auto elim:distance_successor_distance)
    have "n \<notin> backward_slice S"
    proof
      assume "n \<in> backward_slice S"
      from `valid_edge a` `n = sourcenode a` have "valid_node n" by simp
      with `n \<in> backward_slice S` have "obs n (backward_slice S) = {n}"
        by -(rule n_in_obs)
      with `obs n (backward_slice S) = {n'}` have "n = n'" by simp
      with `valid_node n` have "n -[]\<rightarrow>* n'" by(fastforce intro:empty_path)
      with `distance n n' (Suc x)` show False
        by(fastforce elim:distance.cases)
    qed
    from `distance (targetnode a) n' x` `n' \<in> backward_slice S`
    obtain m where "m \<in> obs (targetnode a) (backward_slice S)"
      by(fastforce elim:distance.cases path_ex_obs)
    from `valid_edge a` `n \<notin> backward_slice S` `n = sourcenode a`
    have "obs (targetnode a) (backward_slice S) \<subseteq> 
      obs (sourcenode a) (backward_slice S)"
      by -(rule edge_obs_subset,auto)
    with `m \<in> obs (targetnode a) (backward_slice S)` `n = sourcenode a`
      `obs n (backward_slice S) = {n'}`
    have "n' \<in> obs (targetnode a) (backward_slice S)" by auto
    hence "obs (targetnode a) (backward_slice S) = {n'}" 
      by(rule obs_singleton_element)
    from IH[OF `distance (targetnode a) n' x` this]
    obtain as where "targetnode a -as\<rightarrow>* n'" and "preds (slice_kinds S as) s"
      and "slice_edges S as = []" by blast
    from `targetnode a -as\<rightarrow>* n'` `valid_edge a` `n = sourcenode a`
    have "n -a#as\<rightarrow>* n'" by(fastforce intro:Cons_path)
    from `slice_edges S as = []` `n \<notin> backward_slice S` `n = sourcenode a`
    have "slice_edges S (a#as) = []" by(simp add:slice_edges_def)
    show ?case
    proof(cases "kind a")
      case (Update f)
      with `n \<notin> backward_slice S` `n = sourcenode a` have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      hence "transfer (slice_kind S a) s = s" and "pred (slice_kind S a) s"
        by simp_all
      with `preds (slice_kinds S as) s` have "preds (slice_kinds S (a#as)) s"
        by(simp add:slice_kinds_def)
      with `n -a#as\<rightarrow>* n'` `slice_edges S (a#as) = []` show ?thesis
        by blast
    next
      case (Predicate Q)
      with `n \<notin> backward_slice S` `n = sourcenode a` `distance n n' (Suc x)`  
        `obs n (backward_slice S) = {n'}` `distance (targetnode a) n' x`
        `targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
        distance (targetnode a') n' x \<and>
        valid_edge a' \<and> targetnode a' = nx)`
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      hence "transfer (slice_kind S a) s = s" and "pred (slice_kind S a) s"
        by simp_all
      with `preds (slice_kinds S as) s` have "preds (slice_kinds S (a#as)) s"
        by(simp add:slice_kinds_def)
      with `n -a#as\<rightarrow>* n'` `slice_edges S (a#as) = []` show ?thesis by blast
    qed
  qed
qed


theorem fundamental_property_of_static_slicing:
  assumes path:"n -as\<rightarrow>* n'" and preds:"preds (kinds as) s" and "n' \<in> S"
  obtains as' where "preds (slice_kinds S as') s"
  and "(\<forall>V \<in> Use n'. state_val (transfers (slice_kinds S as') s) V = 
                     state_val (transfers (kinds as) s) V)"
  and "slice_edges S as = slice_edges S as'" and "n -as'\<rightarrow>* n'"
proof(atomize_elim)
  from path preds obtain n'' s'' as' as''
    where "S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')"
    and "S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)"
    and "slice_edges S as = slice_edges S as''"
    and "n -as''@as'\<rightarrow>* n'"
    by -(erule_tac S="S" in path_trans_observable_moves,auto)
  from path have "valid_node n" and "valid_node n'" 
    by(fastforce dest:path_valid_node)+
  from `valid_node n` have "((n,s),(n,s)) \<in> WS S" by(fastforce intro:WSI)
  from `valid_node n'` `n' \<in> S` have "obs n' (backward_slice S) = {n'}"
    by(fastforce intro!:n_in_obs refl)
  from `valid_node n'` have "n'-[]\<rightarrow>* n'" by(fastforce intro:empty_path)
  with `valid_node n'` `n' \<in> S` have "\<forall>V \<in> Use n'. V \<in> rv S n'"
    by(fastforce intro:rvI refl simp:sourcenodes_def)
  show "\<exists>as'. preds (slice_kinds S as') s \<and>
    (\<forall>V \<in> Use n'. state_val (transfers (slice_kinds S as') s) V = 
                  state_val (transfers (kinds as) s) V) \<and>
    slice_edges S as = slice_edges S as' \<and> n -as'\<rightarrow>* n'"
  proof(cases "slice_edges S as = []")
    case True
    hence "preds (slice_kinds S []) s" and "slice_edges S [] = slice_edges S as"
      by(simp_all add:slice_kinds_def slice_edges_def)
    from `S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')` True
    have "n = n''" and "s = s''"
      by(fastforce elim:trans_observable_moves.cases)+
    with `S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
    have "S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)" by simp
    with `valid_node n` have "n -as'\<rightarrow>* n'"
      by(fastforce dest:silent_moves_preds_transfers_path)
    from `S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
    have "slice_edges S as' = []" by(fastforce dest:silent_moves_no_slice_edges)
    with `n -as'\<rightarrow>* n'` `valid_node n'` `n' \<in> S` obtain asx
      where "n -asx\<rightarrow>* n'" and "preds (slice_kinds S asx) s"
      and "slice_edges S asx = []"
      by -(erule exists_sliced_path_preds,auto intro:refl)
    from `S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
      `((n,s),(n,s)) \<in> WS S` `obs n' (backward_slice S) = {n'}`
    have "((n',transfers (kinds as) s),(n,s)) \<in> WS S"
      by(fastforce intro:WS_silent_moves)
    with True have "\<forall>V \<in> rv S n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V"
      by(fastforce dest:WSD simp:slice_edges_def slice_kinds_def)
    with `\<forall>V \<in> Use n'. V \<in> rv S n'`
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V" by simp
    with `slice_edges S asx = []` `slice_edges S [] = slice_edges S as`
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S asx)) s) V"
      by(simp add:slice_edges_def)
    hence "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S asx) s) V"
      by(simp add:transfers_slice_kinds_slice_edges)
    with `n -asx\<rightarrow>* n'` `preds (slice_kinds S asx) s`
      `slice_edges S asx = []` `slice_edges S [] = slice_edges S as`
    show ?thesis
      by(rule_tac x="asx" in exI,simp add:slice_edges_def)
  next
    case False
    with `S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')` `((n,s),(n,s)) \<in> WS S`
    have "((n'',s''),(n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S"
      "S,slice_kind S \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* 
      (n'',transfers (slice_kinds S (slice_edges S as)) s)"
      by(fastforce dest:WS_weak_sim_trans)+
    from `S,slice_kind S \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* 
                             (n'',transfers (slice_kinds S (slice_edges S as)) s)`
      `valid_node n`
    obtain asx where "preds (slice_kinds S asx) s" 
      and "slice_edges S asx = slice_edges S as"
      and "n -asx\<rightarrow>* n''"
      by(fastforce elim:trans_observable_moves_preds simp:slice_kinds_def)
    from `n -asx\<rightarrow>* n''` have "valid_node n''" by(fastforce dest:path_valid_node)
    with `S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
    have "n'' -as'\<rightarrow>* n'"
      by(fastforce dest:silent_moves_preds_transfers_path)
    from `S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
    have "slice_edges S as' = []" by(fastforce dest:silent_moves_no_slice_edges)
    with `n'' -as'\<rightarrow>* n'` `valid_node n'` `n' \<in> S` obtain asx'
      where "n'' -asx'\<rightarrow>* n'" and "slice_edges S asx' = []"
      and "preds (slice_kinds S asx') (transfers (slice_kinds S asx) s)"
      by -(erule exists_sliced_path_preds,auto intro:refl)
    from `n -asx\<rightarrow>* n''` `n'' -asx'\<rightarrow>* n'` have "n -asx@asx'\<rightarrow>* n'"
      by(rule path_Append)
    from `slice_edges S asx = slice_edges S as` `slice_edges S asx' = []`
    have "slice_edges S as = slice_edges S (asx@asx')"
      by(auto simp:slice_edges_def)
    from `preds (slice_kinds S asx') (transfers (slice_kinds S asx) s)`
      `preds (slice_kinds S asx) s`
    have "preds (slice_kinds S (asx@asx')) s" 
      by(simp add:slice_kinds_def preds_split)
    from `obs n' (backward_slice S) = {n'}`
      `S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)`
      `((n'',s''),(n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S`
    have "((n',transfers (kinds as) s),
      (n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S"
      by(fastforce intro:WS_silent_moves)
    hence "\<forall>V \<in> rv S n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V"
      by(fastforce dest:WSD)
    with `\<forall>V \<in> Use n'. V \<in> rv S n'` `slice_edges S asx = slice_edges S as`
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S asx)) s) V"
      by fastforce
    with `slice_edges S asx' = []`
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S (asx@asx'))) s) V"
      by(auto simp:slice_edges_def)
    hence "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (asx@asx')) s) V"
      by(simp add:transfers_slice_kinds_slice_edges)
    with `preds (slice_kinds S (asx@asx')) s` `n -asx@asx'\<rightarrow>* n'`
      `slice_edges S as = slice_edges S (asx@asx')`
    show ?thesis by simp blast
  qed
qed


end


subsection {* The fundamental property of (static) slicing related to the semantics *}

locale BackwardSlice_wf = 
  BackwardSlice sourcenode targetnode kind valid_edge Entry Def Use state_val 
  backward_slice +
  CFG_semantics_wf sourcenode targetnode kind valid_edge Entry sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node set \<Rightarrow> 'node set" 
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80)

begin


theorem fundamental_property_of_path_slicing_semantically:
  assumes "n \<triangleq> c" and "\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"
  obtains n' as where "n -as\<rightarrow>* n'" and "preds (slice_kinds {n'} as) s" and "n' \<triangleq> c'"
  and "\<forall>V \<in> Use n'. state_val (transfers (slice_kinds {n'} as) s) V = state_val s' V"
proof(atomize_elim)
  from `n \<triangleq> c` `\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>` obtain n' as where "n -as\<rightarrow>* n'"
    and "transfers (kinds as) s = s'" and "preds (kinds as) s" and "n' \<triangleq> c'"
    by(fastforce dest:fundamental_property)
  from `n -as\<rightarrow>* n'` `preds (kinds as) s` obtain as'
    where "preds (slice_kinds {n'} as') s"
    and vals:"\<forall>V \<in> Use n'. state_val (transfers (slice_kinds {n'} as') s) V = 
    state_val (transfers (kinds as) s) V" and "n -as'\<rightarrow>* n'"
    by -(erule fundamental_property_of_static_slicing,auto)
  from `transfers (kinds as) s = s'` vals have "\<forall>V \<in> Use n'.
    state_val (transfers (slice_kinds {n'} as') s) V = state_val s' V"
    by simp
  with `preds (slice_kinds {n'} as') s` `n -as'\<rightarrow>* n'` ` n' \<triangleq> c'`
  show "\<exists>as n'. n -as\<rightarrow>* n' \<and> preds (slice_kinds {n'} as) s \<and> n' \<triangleq> c' \<and>
    (\<forall>V\<in>Use n'. state_val (transfers (slice_kinds {n'} as) s) V = state_val s' V)"
    by blast
qed


end

end
