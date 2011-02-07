theory Worklist
imports While_Combinator
begin

definition
  worklist2 :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> 's)
    \<Rightarrow> 'a list * 's \<Rightarrow> ('a list * 's)option"
where
"worklist2 succs accum =
 while_option 
   (%(ws,s). ws \<noteq> [])
   (%(ws,s). case ws of x#ws' \<Rightarrow> (succs x @ ws', accum s x))"

abbreviation succs_rel :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('a * 'a)set" where
"succs_rel f == {(x,y). y : set(f x)}"

lemma Image_succs_rel_set:
  "(succs_rel succs)^* `` set(succs x) = (succs_rel succs)^+ `` {x}"
by(auto simp add: trancl_unfold_left)

lemma worklist_end_empty:
  "worklist2 succs accum (ws0,s0) = Some(ws,s) \<Longrightarrow> ws = []"
unfolding worklist2_def
by (drule while_option_stop) simp

theorem worklist2:
assumes "worklist2 succs accum (ws\<^isub>0,s\<^isub>0) = Some(ws,s)"
shows "EX done. set done = ((succs_rel succs)^*) `` (set ws\<^isub>0) &
              s = foldl accum s\<^isub>0 done"
proof -
  let ?b = "%(ws,s). ws \<noteq> []"
  let ?c = "%(ws,s). case ws of x#ws' \<Rightarrow> (succs x @ ws', accum s x)"
  let ?Q = "% ws s done.
    s = foldl accum s\<^isub>0 done &
      ((succs_rel succs)^*) `` (set ws\<^isub>0) =
          set done Un ((succs_rel succs)^*) `` set ws"
  let ?P = "%(ws,s). EX done. ?Q ws s done"
  have 0: "while_option ?b ?c (ws\<^isub>0,s\<^isub>0) = Some(ws,s)"
    using assms by(simp add: worklist2_def)
  from while_option_stop[OF 0] have "ws = []" by simp
  have init: "?P (ws\<^isub>0,s\<^isub>0)"
    apply auto
    apply(rule_tac x = "[]" in exI)
    apply simp
    done
  { fix ws s
    assume "?P (ws,s)"
    then obtain "done" where "?Q ws s done" by blast
    assume "?b(ws,s)"
    then obtain x ws' where "ws = x # ws'" by(auto simp: neq_Nil_conv)
    then have "?Q (succs x @ ws') (accum s x) (done @ [x])"
      using `?Q ws s done`
      apply simp
      apply(erule thin_rl)+
      apply (auto simp add: Image_Un Image_succs_rel_set)
      apply (blast elim: rtranclE intro: rtrancl_into_trancl1)
      done
    hence "?P(?c(ws,s))" using `ws=x#ws'`
      by(simp only: split_conv list.cases) blast
  }
  then have "?P(ws,s)"
    using while_option_rule[where P="?P", OF _ 0 init]
    by auto
  then show ?thesis using `ws=[]` by auto
qed

definition "worklist succs accum todo s =
  (case worklist2 succs accum (todo,s) of
     None \<Rightarrow> None | Some(ws,s) \<Rightarrow> Some s)"

theorem worklist:
  "worklist succs accum ws\<^isub>0 s\<^isub>0 = Some s \<Longrightarrow>
   EX done. set done = ((succs_rel succs)^*) `` (set ws\<^isub>0) &
              s = foldl accum s\<^isub>0 done"
by(simp add: worklist_def worklist2 split: option.splits prod.splits)

end
