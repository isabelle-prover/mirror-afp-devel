section \<open>Sorted Contexts\<close>

theory Sorted_Contexts
  imports
    First_Order_Terms.Subterm_and_Context
    Sorted_Terms
begin

fun aContext where
  "aContext F A (Hole,\<sigma>) = Some \<sigma>"
| "aContext F A (More f ls C rs, \<sigma>) = do {
    \<rho>s \<leftarrow> those (map A ls);
    \<mu> \<leftarrow> aContext F A (C,\<sigma>);
    \<nu>s \<leftarrow> those (map A rs);
    F (f, \<rho>s @ \<mu> # \<nu>s)}"

lemma Hole_hastype[simp]: "Hole : \<sigma> \<rightarrow> \<tau> in aContext F A \<longleftrightarrow> \<sigma> = \<tau>"
  and More_hastype: "More f ls C rs : \<sigma> \<rightarrow> \<tau> in aContext F A \<longleftrightarrow> (\<exists>\<rho>s \<mu> \<nu>s.
    f : \<rho>s @ \<mu> # \<nu>s \<rightarrow> \<tau> in F \<and>
    ls :\<^sub>l \<rho>s in A \<and>
    C : \<sigma> \<rightarrow> \<mu> in aContext F A \<and>
    rs :\<^sub>l \<nu>s in A)"
   by (auto simp: hastype_list_iff_those bind_eq_Some_conv fun_hastype_def
       intro!: hastypeI)

lemma More_hastypeI:
  assumes "f : \<rho>s @ \<mu> # \<nu>s \<rightarrow> \<tau> in F"
    and "ls :\<^sub>l \<rho>s in A"
    and "C : \<sigma> \<rightarrow> \<mu> in aContext F A"
    and "rs :\<^sub>l \<nu>s in A"
  shows "More f ls C rs : \<sigma> \<rightarrow> \<tau> in aContext F A"
  using assms by (auto simp: More_hastype)

lemma hastype_aContext_induct[consumes 1, case_names Hole More]:
  assumes C: "C : \<sigma> \<rightarrow> \<tau> in aContext F A"
    and hole: "P \<box> \<sigma>"
    and more: "\<And>f \<mu>s \<rho> \<nu>s \<tau> ls C rs.
      f : \<mu>s @ \<rho> # \<nu>s \<rightarrow> \<tau> in F \<Longrightarrow>
      ls :\<^sub>l \<mu>s in A \<Longrightarrow>
      C : \<sigma> \<rightarrow> \<rho> in aContext F A \<Longrightarrow>
      P C \<rho> \<Longrightarrow>
      rs :\<^sub>l \<nu>s in A \<Longrightarrow>
      P (More f ls C rs) \<tau>"
  shows "P C \<tau>"
  using C
proof (induct C arbitrary: \<tau>)
  case Hole
  with hole show ?case by auto
next
  case (More f ls C rs)
  from \<open>More f ls C rs : \<sigma> \<rightarrow> \<tau> in aContext F A\<close>
    [unfolded More_hastype]
  obtain \<rho>s \<mu> \<nu>s
    where f: "f : \<rho>s @ \<mu> # \<nu>s \<rightarrow> \<tau> in F"
      and ls: "ls :\<^sub>l \<rho>s in A"
      and C: "C : \<sigma> \<rightarrow> \<mu> in aContext F A"
      and rs: "rs :\<^sub>l \<nu>s in A" by auto
  show ?case
    using More(1)[OF C] more[OF f ls C _ rs]
    by (auto simp: bind_eq_Some_conv)
qed


context sorted_algebra begin

lemma intp_ctxt_hastype:
  assumes C: "C : \<sigma> \<rightarrow> \<tau> in aContext F A" and a: "a : \<sigma> in A"
  shows "I\<langle>C;a\<rangle> : \<tau> in A"
  using C
proof (induct arbitrary: \<tau>)
  case Hole
  with a show ?case by simp
next
  case (More f ls C rs)
  then show ?case by (auto intro!: sort_matches list_all2_appendI simp: More_hastype)
qed

lemma ctxt_has_same_type:
  assumes C: "C : \<sigma> \<rightarrow> \<tau> in aContext F A" and "a : \<sigma> in A"
  shows "I\<langle>C;a\<rangle> : \<tau>' in A \<longleftrightarrow> \<tau>' = \<tau>"
  using assms by (auto simp: has_same_type intp_ctxt_hastype)

end

lemma subt_in_dom:
  assumes s: "s \<in> dom \<T>(F,V)" and st: "s \<unrhd> t" shows "t \<in> dom \<T>(F,V)"
  using st s
proof (induction)
  case (refl t)
  then show ?case.
next
  case (subt u ss t f)
  from Fun_in_dom_imp_arg_in_dom[OF \<open>Fun f ss \<in> dom \<T>(F,V)\<close> \<open>u \<in> set ss\<close>] subt.IH
  show ?case by auto
qed

text \<open>Term contexts are abstract contexts in the term algebra.\<close>

abbreviation Context ("(2\<C>'(_,/_'))" [1,1]50) where
  "\<C>(F,V) \<equiv> aContext F \<T>(F,V)"

lemmas hastype_context_apply = term.intp_ctxt_hastype

lemma hastype_context_decompose:
  assumes "C\<langle>t\<rangle> : \<tau> in \<T>(F,V)"
  shows "\<exists> \<sigma>. C : \<sigma> \<rightarrow> \<tau> in \<C>(F,V) \<and> t : \<sigma> in \<T>(F,V)"
  using assms
proof (induct C arbitrary: \<tau>)
  case Hole
  then show ?case by auto
next
  case (More f bef C aft \<tau>)
  from More(2) have "Fun f (bef @ C\<langle>t\<rangle> # aft) : \<tau> in \<T>(F,V)" by auto
  from this[unfolded Fun_hastype] obtain \<sigma>s where
    f: "f : \<sigma>s \<rightarrow> \<tau> in F" and list: "bef @ C\<langle>t\<rangle> # aft :\<^sub>l \<sigma>s in \<T>(F,V)" 
    by auto
  from list have len: "length \<sigma>s = length bef + Suc (length aft)"
    by (simp add: list_all2_conv_all_nth)
  let ?i = "length bef" 
  from len have "?i < length \<sigma>s" by auto
  hence id: "take ?i \<sigma>s @ \<sigma>s ! ?i # drop (Suc ?i) \<sigma>s = \<sigma>s"
    by (metis id_take_nth_drop)
  from list have Ct: "C\<langle>t\<rangle> : \<sigma>s ! ?i in \<T>(F,V)"
    by (metis (no_types, lifting) list_all2_Cons1 list_all2_append1 nth_append_length)
  from list have bef: "bef :\<^sub>l take ?i \<sigma>s in \<T>(F,V)"
    by (metis (no_types, lifting) append_eq_conv_conj list_all2_append1)
  from list have aft: "aft :\<^sub>l drop (Suc ?i) \<sigma>s in \<T>(F,V)"
    by (metis (no_types, lifting) Cons_nth_drop_Suc append_eq_conv_conj drop_all length_greater_0_conv linorder_le_less_linear list.rel_inject(2) list.simps(3) list_all2_append1)
  from More(1)[OF Ct] obtain \<sigma> where C: "C : \<sigma> \<rightarrow> \<sigma>s ! ?i in \<C>(F,V)" and t: "t : \<sigma> in \<T>(F,V)" 
    by auto
  show ?case 
    by (intro exI[of _ \<sigma>] conjI More_hastypeI[OF _ bef _ aft, of _ "\<sigma>s ! ?i"] C t, unfold id, rule f)
qed

lemma apply_ctxt_in_dom_imp_in_dom:
  assumes "C\<langle>t\<rangle> \<in> dom \<T>(F,V)" 
  shows "t \<in> dom \<T>(F,V)"
  apply (rule subt_in_dom[OF assms]) by simp

lemma apply_ctxt_hastype_imp_hastype_context:
  assumes C: "C\<langle>t\<rangle> : \<tau> in \<T>(F,V)" and t: "t : \<sigma> in \<T>(F,V)"
  shows "C : \<sigma> \<rightarrow> \<tau> in \<C>(F,V)"
  using hastype_context_decompose[OF C] t by (auto simp: has_same_type)

lemma subst_apply_ctxt_sorted:
  assumes "C : \<sigma> \<rightarrow> \<tau> in \<C>(F,X)" and "\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V)"
  shows "C \<cdot>\<^sub>c \<theta> : \<sigma> \<rightarrow> \<tau> in \<C>(F,V)"
  using assms
proof(induct arbitrary: \<theta> rule: hastype_aContext_induct)
  case (Hole)
  then show ?case by simp
next
  case (More f \<sigma>b \<rho> \<sigma>a \<tau> bef C aft)
  have fssig: "f : \<sigma>b @ \<rho> # \<sigma>a \<rightarrow> \<tau> in F" using More(1) .
  have bef:"bef :\<^sub>l \<sigma>b in \<T>(F,X)" using More(2) .
  have Cssig:"C : \<sigma> \<rightarrow> \<rho> in \<C>(F,X)" using More(3) .
  have aft:"aft :\<^sub>l \<sigma>a in \<T>(F,X)" using More(5) .
  have theta:"\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V)" using More(6) .
  hence ctheta:"C \<cdot>\<^sub>c \<theta> : \<sigma> \<rightarrow> \<rho> in \<C>(F,V)" using More(4) by simp
  have len_bef:"length bef = length \<sigma>b" using bef list_all2_iff by blast
  have len_aft:"length aft = length \<sigma>a" using aft list_all2_iff by blast
  { fix i
    assume len_i:"i < length \<sigma>b"
    hence "bef ! i \<cdot> \<theta> : \<sigma>b ! i in \<T>(F,V)"
    proof -
      have "bef ! i : \<sigma>b ! i in \<T>(F,X)" using bef
        by (simp add: len_i list_all2_conv_all_nth)
      from subst_hastype[OF theta this] 
      show ?thesis.
    qed
  } note * = this
  have mb: "map (\<lambda>t. t \<cdot> \<theta>) bef :\<^sub>l \<sigma>b in \<T>(F,V)" using length_map 
    by (auto simp:* theta bef list_all2_conv_all_nth len_bef)
  { fix i
    assume len_i:"i < length \<sigma>a"
    hence "aft ! i \<cdot> \<theta> : \<sigma>a ! i in \<T>(F,V)"
    proof -
      have "aft ! i : \<sigma>a ! i in \<T>(F,X)" using aft
        by (simp add: len_i list_all2_conv_all_nth)
      from subst_hastype[OF theta this] 
      show ?thesis.
    qed
  } note ** = this
  have ma: "map (\<lambda>t. t \<cdot> \<theta>) aft :\<^sub>l \<sigma>a in \<T>(F,V)" using length_map
    by (auto simp:** theta aft list_all2_conv_all_nth len_aft)
  show "More f bef C aft \<cdot>\<^sub>c \<theta> : \<sigma> \<rightarrow> \<tau> in \<C>(F,V)"
    by (auto intro!: More_hastypeI fssig simp:ctheta mb ma)
qed

end