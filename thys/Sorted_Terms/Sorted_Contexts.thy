section \<open>Sorted Contexts\<close>

theory Sorted_Contexts
  imports
    First_Order_Terms.Subterm_and_Context
    Sorted_Terms
begin

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


(* sorted contexts *)

inductive has_type_context :: "('f,'s) ssig \<Rightarrow> ('v \<rightharpoonup> 's) \<Rightarrow> 's \<Rightarrow> ('f,'v)ctxt \<Rightarrow> 's \<Rightarrow> bool"
   for F V \<sigma> where
  Hole: "has_type_context F V \<sigma> Hole \<sigma>"
| More: "f : \<sigma>b @ \<rho> # \<sigma>a \<rightarrow> \<tau> in F \<Longrightarrow>
  bef :\<^sub>l \<sigma>b in \<T>(F,V) \<Longrightarrow> has_type_context F V \<sigma> C \<rho> \<Longrightarrow> aft :\<^sub>l \<sigma>a in \<T>(F,V) \<Longrightarrow>
  has_type_context F V \<sigma> (More f bef C aft) \<tau>" 

hide_fact (open) Hole More

abbreviation has_type_context' (\<open>((_) :\<^sub>c/ (_) \<rightarrow> (_) in/ \<T>'(_,_'))\<close> [50,61,51,51,51]50)
  where "C :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V) \<equiv> has_type_context F V \<sigma> C \<tau>"

lemma hastype_context_apply:
  assumes "C :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V)" and "t : \<sigma> in \<T>(F,V)" 
  shows "C\<langle>t\<rangle> : \<tau> in \<T>(F,V)"
  using assms
proof induct
  case (More f \<sigma>b \<rho> \<sigma>a \<tau> bef C aft)
  show ?case unfolding intp_actxt.simps
  proof (intro Fun_hastypeI[OF More(1)])
    show "bef @ C\<langle>t\<rangle> # aft :\<^sub>l \<sigma>b @ \<rho> # \<sigma>a in \<T>(F,V)" 
      using More(2,5) More(4)[OF More(6)]
      by (simp add: list_all2_appendI)
  qed
qed auto

lemma hastype_context_decompose:
  assumes "C\<langle>t\<rangle> : \<tau> in \<T>(F,V)"
  shows "\<exists> \<sigma>. C :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V) \<and> t : \<sigma> in \<T>(F,V)"
  using assms
proof (induct C arbitrary: \<tau>)
  case Hole
  then show ?case by (auto intro: has_type_context.Hole)
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
  from More(1)[OF Ct] obtain \<sigma> where C: "C :\<^sub>c \<sigma> \<rightarrow> \<sigma>s ! ?i in \<T>(F,V)" and t: "t : \<sigma> in \<T>(F,V)" 
    by auto
  show ?case 
    by (intro exI[of _ \<sigma>] conjI has_type_context.More[OF _ bef _ aft, of _ "\<sigma>s ! ?i"] C t, unfold id, rule f)
qed

lemma apply_ctxt_in_dom_imp_in_dom:
  assumes "C\<langle>t\<rangle> \<in> dom \<T>(F,V)" 
  shows "t \<in> dom \<T>(F,V)"
  apply (rule subt_in_dom[OF assms]) by simp

lemma apply_ctxt_hastype_imp_hastype_context:
  assumes C: "C\<langle>t\<rangle> : \<tau> in \<T>(F,V)" and t: "t : \<sigma> in \<T>(F,V)"
  shows "C :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V)"
  using hastype_context_decompose[OF C] t by (auto simp: has_same_type)

lemma subst_apply_ctxt_sorted:
  assumes "C :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,X)" and "\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V)"
  shows "C \<cdot>\<^sub>c \<theta> :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V)"
  using assms
proof(induct arbitrary: \<theta> rule: has_type_context.induct)
  case (Hole)
  then show ?case by (simp add: has_type_context.Hole)
next
  case (More f \<sigma>b \<rho> \<sigma>a \<tau> bef C aft)
  have fssig: "f : \<sigma>b @ \<rho> # \<sigma>a \<rightarrow> \<tau> in F" using More(1) .
  have bef:"bef :\<^sub>l \<sigma>b in \<T>(F,X)" using More(2) .
  have Cssig:"C :\<^sub>c \<sigma> \<rightarrow> \<rho> in \<T>(F,X)" using More(3) .
  have aft:"aft :\<^sub>l \<sigma>a in \<T>(F,X)" using More(5) .
  have theta:"\<theta> :\<^sub>s X \<rightarrow> \<T>(F,V)" using More(6) .
  hence ctheta:"C \<cdot>\<^sub>c \<theta> :\<^sub>c \<sigma> \<rightarrow> \<rho> in \<T>(F,V)" using More(4) by simp
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
  show "More f bef C aft \<cdot>\<^sub>c \<theta> :\<^sub>c \<sigma> \<rightarrow> \<tau> in \<T>(F,V)"
    by (auto intro!: has_type_context.intros fssig simp:ctheta mb ma)
qed

end