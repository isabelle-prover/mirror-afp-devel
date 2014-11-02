section {* Distance of Paths *}

theory Distance imports CFG begin

context CFG begin

inductive distance :: "'node \<Rightarrow> 'node \<Rightarrow> nat \<Rightarrow> bool"
where distanceI:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<iota>* n'; length as = x; \<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'\<rbrakk>
  \<Longrightarrow> distance n n' x"


lemma every_path_distance:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'"
  obtains x where "distance n n' x" and "x \<le> length as"
proof(atomize_elim)
  show "\<exists>x. distance n n' x \<and> x \<le> length as"
  proof(cases "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> 
                     (\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx)")
    case True
    then obtain as' 
      where "n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> (\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx)" 
      by blast
    hence "n -as'\<rightarrow>\<^sub>\<iota>* n'" and all:"\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx"
      by simp_all
    hence "distance n n' (length as')" by(fastforce intro:distanceI)
    from `n -as\<rightarrow>\<^sub>\<iota>* n'` all have "length as' \<le> length as" by fastforce
    with `distance n n' (length as')` show ?thesis by blast
  next
    case False
    hence all:"\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> (\<exists>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<and> length as' > length asx)"
      by fastforce
    have "wf (measure length)" by simp
    from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "as \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" by simp
    with `wf (measure length)` obtain as' where "as' \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" 
      and notin:"\<And>as''. (as'',as') \<in> (measure length) \<Longrightarrow> as'' \<notin> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}"
      by(erule wfE_min)
    from `as' \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}` have "n -as'\<rightarrow>\<^sub>\<iota>* n'" by simp
    with all obtain asx where "n -asx\<rightarrow>\<^sub>\<iota>* n'"
      and "length as' > length asx"
      by blast
    with notin have  "asx \<notin> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" by simp
    hence "\<not> n -asx\<rightarrow>\<^sub>\<iota>* n'" by simp
    with `n -asx\<rightarrow>\<^sub>\<iota>* n'` have False by simp
    thus ?thesis by simp
  qed
qed


lemma distance_det:
  "\<lbrakk>distance n n' x; distance n n' x'\<rbrakk> \<Longrightarrow> x = x'"
apply(erule distance.cases)+ apply clarsimp
apply(erule_tac x="asa" in allE) apply(erule_tac x="as" in allE)
by simp


lemma only_one_SOME_dist_edge:
  assumes "valid_edge a" and "intra_kind(kind a)" and "distance (targetnode a) n' x"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and>
               valid_edge a' \<and> intra_kind(kind a') \<and>
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' x \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and> 
                                              targetnode a' = nx)"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> 
             distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
             targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            distance (targetnode a') n' x \<and>
                                            valid_edge a' \<and> intra_kind(kind a') \<and> 
                                            targetnode a' = nx)"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> 
                distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
                targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                               distance (targetnode a') n' x \<and>
                                               valid_edge a' \<and> intra_kind(kind a') \<and> 
                                               targetnode a' = nx)) =
      (\<exists>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and> 
                 valid_edge a' \<and> intra_kind(kind a') \<and> targetnode a' = nx)"
      apply(unfold some_eq_ex[of "\<lambda>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
        distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and> 
        targetnode a' = nx"])
      by simp
    also have "\<dots>" 
      using `valid_edge a` `intra_kind(kind a)` `distance (targetnode a) n' x`
      by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> 
    distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and> 
    targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> intra_kind(kind a') \<and> 
                                   targetnode a' = nx)"
    and "sourcenode a = sourcenode ax \<and> 
    distance (targetnode ax) n' x \<and> valid_edge ax \<and> intra_kind(kind ax) \<and> 
    targetnode ax = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> intra_kind(kind a') \<and> 
                                   targetnode a' = nx)"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma distance_successor_distance:
  assumes "distance n n' x" and "x \<noteq> 0" 
  obtains a where "valid_edge a" and "n = sourcenode a" and "intra_kind(kind a)"
  and "distance (targetnode a) n' (x - 1)"
  and "targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') n' (x - 1) \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = nx)"
proof(atomize_elim)
  show "\<exists>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
    distance (targetnode a) n' (x - 1) \<and>
    targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                  distance (targetnode a') n' (x - 1) \<and>
                                  valid_edge a' \<and> intra_kind(kind a') \<and>
                                  targetnode a' = nx)"
  proof(rule ccontr)
    assume "\<not> (\<exists>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
                   distance (targetnode a) n' (x - 1) \<and> 
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx))"
    hence imp:"\<forall>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx)
                 \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)" by blast
    from `distance n n' x` obtain as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "x = length as"
      and all:"\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from `n -as\<rightarrow>\<^sub>\<iota>* n'` have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
      by(simp_all add:intra_path_def)
    from this `x = length as` all imp show False
    proof(induct rule:path.induct)
      case (empty_path n)
      from `x = length []` `x \<noteq> 0` show False by simp
    next
      case (Cons_path n'' as n' a n)
      note imp = `\<forall>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind (kind a) \<and>
                      targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx)
                    \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)`
      note all = `\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'`
      from `\<forall>a\<in>set (a#as). intra_kind (kind a)` 
      have "intra_kind (kind a)" and "\<forall>a\<in>set as. intra_kind (kind a)"
        by simp_all
      from `n'' -as\<rightarrow>* n'` `\<forall>a\<in>set as. intra_kind (kind a)`
      have "n'' -as\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
      then obtain y where "distance n'' n' y"
        and "y \<le> length as" by(erule every_path_distance)
      from `distance n'' n' y` obtain as' where "n'' -as'\<rightarrow>\<^sub>\<iota>* n'"
        and "y = length as'" by(auto elim:distance.cases)
      hence "n'' -as'\<rightarrow>* n'" and "\<forall>a\<in>set as'. intra_kind (kind a)"
        by(simp_all add:intra_path_def)
      show False
      proof(cases "y < length as")
        case True
        from `valid_edge a` `sourcenode a = n` `targetnode a = n''` `n'' -as'\<rightarrow>* n'`
        have "n -a#as'\<rightarrow>* n'" by -(rule path.Cons_path)
        with `\<forall>a\<in>set as'. intra_kind (kind a)` `intra_kind (kind a)`
        have "n -a#as'\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
        with all have "x \<le> length (a#as')" by blast
        with `x = length (a#as)` True `y = length as'` show False by simp
      next
        case False
        with `y \<le> length as` `x = length (a#as)` have "y = x - 1" by simp
        from `targetnode a = n''` `distance n'' n' y`
        have "distance (targetnode a) n' y" by simp
        with `valid_edge a` `intra_kind(kind a)`
        obtain a' where "sourcenode a = sourcenode a'"
          and "distance (targetnode a') n' y" and "valid_edge a'"
          and "intra_kind(kind a')"
          and "targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' y \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and>
                                              targetnode a' = nx)"
          by(auto dest:only_one_SOME_dist_edge)
        with imp `sourcenode a = n` `y = x - 1` show False by fastforce
      qed
    qed
  qed
qed

end

end
