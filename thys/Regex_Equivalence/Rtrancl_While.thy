(*  Author: Tobias Nipkow, Dmitriy Traytel *)

header "Transitive Closure"

(*<*)
theory Rtrancl_While
imports "~~/src/HOL/Library/While_Combinator"
begin
(*>*)

text{* Computing the reflexive, transitive closure by iterating a successor
function. Stops when an element is found that dos not satisfy the test.

More refined (and hence more efficient) versions can be found in ITP 2011 paper
by Nipkow (the theories are in the AFP entry Flyspeck by Nipkow)
and the AFP article Executable Transitive Closures by René Thiemann. *}

context
fixes p :: "'a \<Rightarrow> bool"
and f :: "'a \<Rightarrow> 'a list"
and x :: 'a
begin

fun rtrancl_while_test :: "'a list \<times> 'a set \<Rightarrow> bool"
where "rtrancl_while_test (ws,_) = (ws \<noteq> [] \<and> p(hd ws))"

fun rtrancl_while_step :: "'a list \<times> 'a set \<Rightarrow> 'a list \<times> 'a set"
where "rtrancl_while_step (ws, Z) =
  (let x = hd ws; new = remdups (filter (\<lambda>y. y \<notin> Z) (f x))
  in (new @ tl ws, set new \<union> Z))"

definition rtrancl_while :: "('a list * 'a set) option"
where "rtrancl_while = while_option rtrancl_while_test rtrancl_while_step ([x],{x})"

fun rtrancl_while_invariant :: "'a list \<times> 'a set \<Rightarrow> bool"
where "rtrancl_while_invariant (ws, Z) =
   (x \<in> Z \<and> set ws \<subseteq> Z \<and> distinct ws \<and> {(x,y). y \<in> set(f x)} `` (Z - set ws) \<subseteq> Z \<and>
    Z \<subseteq> {(x,y). y \<in> set(f x)}^* `` {x} \<and> (\<forall>z\<in>Z - set ws. p z))"

lemma rtrancl_while_invariant: 
  assumes inv: "rtrancl_while_invariant st" and test: "rtrancl_while_test st"
  shows   "rtrancl_while_invariant (rtrancl_while_step st)"
proof (cases st)
  fix ws Z assume st: "st = (ws, Z)"
  with test obtain h t where "ws = h # t" "p h" by (cases ws) auto
  with inv st show ?thesis by (auto intro: rtrancl.rtrancl_into_rtrancl)
qed

lemma rtrancl_while_Some: assumes "rtrancl_while = Some(ws,Z)"
shows "if ws = []
       then Z = {(x,y). y \<in> set(f x)}^* `` {x} \<and> (\<forall>z\<in>Z. p z)
       else \<not>p(hd ws) \<and> hd ws \<in> {(x,y). y \<in> set(f x)}^* `` {x}"
proof -
  have "rtrancl_while_invariant ([x],{x})" by simp
  with rtrancl_while_invariant have I: "rtrancl_while_invariant (ws,Z)"
    by (rule while_option_rule[OF _ assms[unfolded rtrancl_while_def]])
  { assume "ws = []"
    hence ?thesis using I
      by (auto simp del:Image_Collect_split dest: Image_closed_trancl)
  } moreover
  { assume "ws \<noteq> []"
    hence ?thesis using I while_option_stop[OF assms[unfolded rtrancl_while_def]]
      by (simp add: subset_iff)
  }
  ultimately show ?thesis by simp
qed

lemma rtrancl_while_finite_Some:
  assumes "finite ({(x, y). y \<in> set (f x)}\<^sup>* `` {x})" (is "finite ?Cl")
  shows "\<exists>y. rtrancl_while = Some y"
proof -
  let ?R = "(\<lambda>(_, Z). card (?Cl - Z)) <*mlex*> (\<lambda>(ws, _). length ws) <*mlex*> {}"
  have "wf ?R" by (blast intro: wf_mlex)
  then show ?thesis unfolding rtrancl_while_def
  proof (rule wf_rel_while_option_Some[of ?R rtrancl_while_invariant])
    fix st assume *: "rtrancl_while_invariant st \<and> rtrancl_while_test st"
    hence I: "rtrancl_while_invariant (rtrancl_while_step st)"
      by (blast intro: rtrancl_while_invariant)
    show "(rtrancl_while_step st, st) \<in> ?R"
    proof (cases st)
      fix ws Z let ?ws = "fst (rtrancl_while_step st)" and ?Z = "snd (rtrancl_while_step st)"
      assume st: "st = (ws, Z)"
      with * obtain h t where ws: "ws = h # t" "p h" by (cases ws) auto
      { assume "remdups (filter (\<lambda>y. y \<notin> Z) (f h)) \<noteq> []"
        then obtain z where "z \<in> set (remdups (filter (\<lambda>y. y \<notin> Z) (f h)))" by fastforce
        with st ws I have "Z \<subset> ?Z" "Z \<subseteq> ?Cl" "?Z \<subseteq> ?Cl" by auto
        with assms have "card (?Cl - ?Z) < card (?Cl - Z)" by (blast intro: psubset_card_mono)
        with st ws have ?thesis unfolding mlex_prod_def by simp
      }
      moreover
      { assume "remdups (filter (\<lambda>y. y \<notin> Z) (f h)) = []"
        with st ws have "?Z = Z" "?ws = t"  by (auto simp: filter_empty_conv)
        with st ws have ?thesis unfolding mlex_prod_def by simp
      }
      ultimately show ?thesis by blast
    qed
  qed (simp_all add: rtrancl_while_invariant)
qed

end

(*<*)
hide_const (open) rtrancl_while_test rtrancl_while_step rtrancl_while_invariant
hide_fact (open) rtrancl_while_invariant

end
(*>*)
