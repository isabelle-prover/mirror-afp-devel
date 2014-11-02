section {* Relations between control dependences *}

theory ControlDependenceRelations 
  imports WeakOrderDependence StandardControlDependence 
begin

context StrongPostdomination begin

lemma standard_control_implies_weak_order: 
  assumes "n controls\<^sub>s n'" shows "n \<longrightarrow>\<^bsub>wod\<^esub> n',(_Exit_)"
proof -
  from `n controls\<^sub>s n'` obtain as a a' as' where "as = a#as'"
    and "n' \<notin> set(sourcenodes as)" and "n -as\<rightarrow>* n'"
    and "n' postdominates (targetnode a)"
    and "valid_edge a'" and "sourcenode a' = n"
    and "\<not> n' postdominates (targetnode a')" 
    by(auto simp:standard_control_dependence_def)
  from `n -as\<rightarrow>* n'` `as = a#as'` have "sourcenode a = n" by(auto elim:path.cases)
  from `n -as\<rightarrow>* n'` `as = a#as'` `n' \<notin> set(sourcenodes as)` have "n \<noteq> n'"
    by(induct rule:path.induct,auto simp:sourcenodes_def)
  from `n -as\<rightarrow>* n'` `as = a#as'` have "valid_edge a"
    by(auto elim:path.cases)
  from `n controls\<^sub>s n'` have "n' \<noteq> (_Exit_)"
    by(fastforce dest:Exit_not_standard_control_dependent)
  from `n -as\<rightarrow>* n'` have "(_Exit_) \<notin> set (sourcenodes as)" by fastforce
  from `n -as\<rightarrow>* n'` have "valid_node n" and "valid_node n'"
    by(auto dest:path_valid_node)
  with `\<not> n' postdominates (targetnode a')` `valid_edge a'`
  obtain asx where "targetnode a' -asx\<rightarrow>* (_Exit_)" and "n' \<notin> set(sourcenodes asx)"
    by(auto simp:postdominate_def)
  with `valid_edge a'` `sourcenode a' = n` have "n -a'#asx\<rightarrow>* (_Exit_)"
    by(fastforce intro:Cons_path)
  with `n \<noteq> n'` `sourcenode a' = n` `n' \<notin> set(sourcenodes asx)`
  have "n' \<notin> set(sourcenodes (a'#asx))" by(simp add:sourcenodes_def)
  from `n' postdominates (targetnode a)` 
  obtain asx' where "targetnode a -asx'\<rightarrow>* n'" by(erule postdominate_implies_path)
  from `n' postdominates (targetnode a)`
  have "\<forall>as'. targetnode a -as'\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as')"
    by(auto simp:postdominate_def)
  with `n' \<noteq> (_Exit_)` `n -as\<rightarrow>* n'` `(_Exit_) \<notin> set (sourcenodes as)`
    `n -a'#asx\<rightarrow>* (_Exit_)` `n' \<notin> set(sourcenodes (a'#asx))`
    `valid_edge a` `sourcenode a = n` `targetnode a -asx'\<rightarrow>* n'`
  show ?thesis by(auto simp:wod_def)
qed

end

end
