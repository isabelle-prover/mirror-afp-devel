theory Tree_Automata_Pumping
  imports Tree_Automata
begin

subsection \<open>Pumping lemma\<close>

(* We need to deal with non deterministic tree automata,
   to show the pumping lemma we need to find cycles on the derivation
   of terms with depth greater than the number of states.

  assumes "card (ta_states A) < depth t" and "finite (ta_states A)"
      and "q \<in> ta_res A t" and "ground t"
    shows "\<exists> s v p. t \<unrhd> s \<and> s \<rhd> v \<and> p \<in> ta_res A v \<and> p \<in> ta_res A s"

  we only get t \<longrightarrow>* q, v \<longrightarrow> p, s \<longrightarrow> p, but we have no chance to conclude
  that the state p appears in the derivation t \<longrightarrow>* q, because our derivation is
  not deterministic and there could be a cycle in the derivation of t which does not
  end in state q.
 *)

abbreviation "derivation_ctxt ts Cs \<equiv> Suc (length Cs) = length ts \<and>
  (\<forall> i < length Cs. (Cs ! i) \<langle>ts ! i\<rangle> = ts ! Suc i)"

abbreviation "derivation_ctxt_st A ts Cs qs \<equiv> length qs = length ts \<and> Suc (length Cs) = length ts \<and>
  (\<forall> i < length Cs. qs ! Suc i |\<in>| ta_der A (Cs ! i)\<langle>Var (qs ! i)\<rangle>)"

abbreviation "derivation_sound A ts qs \<equiv> length qs = length ts \<and>
  (\<forall> i < length qs. qs ! i |\<in>| ta_der A (ts ! i))"
 
definition "derivation A ts Cs qs \<longleftrightarrow> derivation_ctxt ts Cs \<and>
  derivation_ctxt_st A ts Cs qs \<and> derivation_sound A ts qs"


(* Context compositions from left *)
lemma ctxt_comp_lhs_not_hole:
  assumes "C \<noteq> \<box>"
  shows "C \<circ>\<^sub>c D \<noteq> \<box>"
  using assms by (cases C; cases D) auto

lemma ctxt_comp_rhs_not_hole:
  assumes "D \<noteq> \<box>"
  shows "C \<circ>\<^sub>c D \<noteq> \<box>"
  using assms by (cases C; cases D) auto

lemma fold_ctxt_comp_nt_empty_acc:
  assumes "D \<noteq> \<box>"
  shows "fold (\<circ>\<^sub>c) Cs D \<noteq> \<box>"
  using assms by (induct Cs arbitrary: D) (auto simp add: ctxt_comp_rhs_not_hole)

lemma fold_ctxt_comp_nt_empty:
  assumes "C \<in> set Cs" and "C \<noteq> \<box>"
  shows "fold (\<circ>\<^sub>c) Cs D \<noteq> \<box>" using assms
  by (induct Cs arbitrary: D) (auto simp: ctxt_comp_lhs_not_hole fold_ctxt_comp_nt_empty_acc)

(* Rep of context *)

lemma empty_ctxt_power [simp]:
  "\<box> ^ n = \<box>"
  by (induct n) auto

lemma ctxt_comp_not_hole:
  assumes "C \<noteq> \<box>" and "n \<noteq> 0"
  shows "C^n \<noteq> \<box>"
  using assms by (induct n arbitrary: C) (auto elim!: ctxt_compose.elims)

lemma ctxt_comp_n_suc [simp]:
  shows "(C^(Suc n))\<langle>t\<rangle> = (C^n)\<langle>C\<langle>t\<rangle>\<rangle>"
  by (induct n arbitrary: C) auto

lemma ctxt_comp_reach:
  assumes "p |\<in>| ta_der A C\<langle>Var p\<rangle>"
  shows "p |\<in>| ta_der A (C^n)\<langle>Var p\<rangle>"
  using assms by (induct n arbitrary: C) (auto intro: ta_der_ctxt)


(* Connecting positions to term depth and trivial depth lemmas *)

lemma args_depth_less [simp]:
  assumes "u \<in> set ss"
  shows "depth u < depth (Fun f ss)" using assms
  by (cases ss) (auto simp: less_Suc_eq_le)

lemma subterm_depth_less:
  assumes "s \<rhd> t"
  shows "depth t < depth s"
  using assms by (induct s t rule: supt.induct) (auto intro: less_trans)

lemma poss_length_depth:
  shows "\<exists> p \<in> poss t. length p = depth t"
proof (induct t)
  case (Fun f ts)
  then show ?case
  proof (cases ts)
    case [simp]: (Cons a list)
    have "ts \<noteq> [] \<Longrightarrow> \<exists> s. f s = Max (f ` set ts) \<and> s \<in> set ts" for ts f
    using Max_in[of "f ` set ts"] by (auto simp: image_iff)
    from this[of ts depth] obtain s where s: "depth s = Max (depth ` set ts) \<and> s \<in> set ts"
      by auto
    then show ?thesis using Fun[of s] in_set_idx[OF conjunct2[OF s]]
      by fastforce
  qed auto
qed auto

lemma poss_length_bounded_by_depth:
  assumes "p \<in> poss t"
  shows "length p \<le> depth t" using assms
  by (induct t arbitrary: p) (auto intro!: Suc_leI, meson args_depth_less dual_order.strict_trans2 nth_mem)

(* Connecting depth to ctxt repetition *)

lemma depth_ctxt_nt_hole_inc:
  assumes "C \<noteq> \<box>"
  shows "depth t < depth C\<langle>t\<rangle>" using assms
  using subterm_depth_less[of t "C\<langle>t\<rangle>"]
  by (simp add: nectxt_imp_supt_ctxt subterm_depth_less) 

lemma depth_ctxt_less_eq:
  "depth t \<le> depth C\<langle>t\<rangle>" using depth_ctxt_nt_hole_inc less_imp_le
  by (cases C, simp) blast  

lemma ctxt_comp_n_not_hole_depth_inc:
  assumes "C \<noteq> \<box>"
  shows "depth (C^n)\<langle>t\<rangle> < depth (C^(Suc n))\<langle>t\<rangle>"
  using assms by (induct n arbitrary: C t) (auto simp: ctxt_comp_not_hole depth_ctxt_nt_hole_inc)

lemma ctxt_comp_n_lower_bound:
  assumes "C \<noteq> \<box>"
  shows "n < depth (C^(Suc n))\<langle>t\<rangle>"
  using assms
proof (induct n arbitrary: C)
  case 0 then show ?case using ctxt_comp_not_hole depth_ctxt_nt_hole_inc gr_implies_not_zero by blast
next
  case (Suc n) then show ?case using ctxt_comp_n_not_hole_depth_inc less_trans_Suc by blast  
qed

lemma ta_der_ctxt_n_loop:
  assumes "q |\<in>| ta_der \<A> t" "q |\<in>| ta_der \<A> C\<langle>Var q\<rangle>"
  shows " q |\<in>| ta_der \<A> (C^n)\<langle>t\<rangle>"
  using assms by (induct n) (auto simp: ta_der_ctxt)

lemma ctxt_compose_funs_ctxt [simp]:
  "funs_ctxt (C \<circ>\<^sub>c D) = funs_ctxt C \<union> funs_ctxt D"
  by (induct C arbitrary: D) auto

lemma ctxt_compose_vars_ctxt [simp]:
  "vars_ctxt (C \<circ>\<^sub>c D) = vars_ctxt C \<union> vars_ctxt D"
  by (induct C arbitrary: D) auto

lemma ctxt_power_funs_vars_0 [simp]:
  assumes "n = 0"
  shows "funs_ctxt (C^n) = {}" "vars_ctxt (C^n) = {}" 
  using assms by auto

lemma ctxt_power_funs_vars_n [simp]:
  assumes "n \<noteq> 0"
  shows "funs_ctxt (C^n) = funs_ctxt C" "vars_ctxt (C^n) = vars_ctxt C" 
  using assms by (induct n arbitrary: C, auto) fastforce+ 


(* Collect all terms in a path via positions *)

fun terms_pos where
  "terms_pos s [] = [s]"
| "terms_pos s (p # ps) = terms_pos (s |_ [p]) ps @ [s]"

lemma subt_at_poss [simp]:
  assumes "a # p \<in> poss s"
  shows "p \<in> poss (s |_ [a])"
  using assms by (metis append_Cons append_self_conv2 poss_append_poss)

lemma terms_pos_length [simp]:
  shows "length (terms_pos t p) = Suc (length p)"
  by (induct p arbitrary: t) auto

lemma terms_pos_last [simp]:
  assumes "i = length p"
  shows "terms_pos t p ! i = t" using assms
  by (induct p arbitrary: t) (auto simp add: append_Cons_nth_middle)

lemma terms_pos_subterm:
  assumes "p \<in> poss t" and "s \<in> set (terms_pos t p)"
  shows "t \<unrhd> s" using assms
  using assms
proof (induct p arbitrary: t s)
  case (Cons a p)
  from Cons(2) have st: "t \<unrhd> t |_ [a]" by auto
  from Cons(1)[of "t |_ [a]"] Cons(2-) show ?case
    using supteq_trans[OF st] by fastforce
qed auto

lemma terms_pos_differ_subterm:
  assumes "p \<in> poss t" and "i < length (terms_pos t p)"
     and "j < length (terms_pos t p)" and "i < j"
   shows "terms_pos t p ! i \<lhd> terms_pos t p ! j"
  using assms
proof (induct p arbitrary: t i j)
  case (Cons a p)
  from Cons(2-) have "t |_ [a] \<unrhd> terms_pos (t |_ [a]) p ! i"
    by (intro terms_pos_subterm[of p]) auto
  from subterm.order.strict_trans1[OF this, of t] Cons(1)[of "t |_ [a]" i j] Cons(2-) show ?case
    by (cases "j = length (a # p)") (force simp add: append_Cons_nth_middle append_Cons_nth_left)+
qed auto

lemma distinct_terms_pos:
  assumes "p \<in> poss t"
  shows "distinct (terms_pos t p)" using assms
proof (induct p arbitrary: t)
  case (Cons a p)
  have "\<And>i. i < Suc (length p) \<Longrightarrow> t \<rhd> (terms_pos (t |_ [a]) p) ! i"
    using terms_pos_differ_subterm[OF Cons(2), of _  "Suc (length p)"] by (auto simp: nth_append) 
  then show ?case using  Cons(1)[of "t |_ [a]"] Cons(2-)
    by (auto simp: in_set_conv_nth) (metis supt_not_sym)
qed auto


lemma term_chain_depth:
  assumes "depth t = n"
  shows "\<exists> p \<in> poss t. length (terms_pos t p) = (n + 1)"
proof -
  obtain p where p: "p \<in> poss t" "length p = depth t"
    using poss_length_depth[of t] by blast
  from terms_pos_length[of t p] this show ?thesis using assms
    by auto
qed

lemma ta_der_derivation_chain_terms_pos_exist:
  assumes "p \<in> poss t" and "q |\<in>| ta_der A t"
  shows "\<exists> Cs qs. derivation A (terms_pos t p) Cs qs \<and> last qs = q"
  using assms         
proof (induct p arbitrary: t q)
  case Nil
  then show ?case by (auto simp: derivation_def intro!: exI[of _ "[q]"])
next
  case (Cons a p)
  from Cons(2) have poss: "p \<in> poss (t |_ [a])" by auto
  from Cons(2) obtain C where C: "C\<langle>t |_ [a]\<rangle> = t"
    using ctxt_at_pos_subt_at_id poss_Cons by blast
  from C ta_der_ctxt_decompose Cons(3) obtain q' where
    res: "q' |\<in>| ta_der A (t |_ [a])" "q |\<in>| ta_der A C\<langle>Var q'\<rangle>"
    by metis
  from Cons(1)[OF _ res(1)] Cons(2-) C obtain Cs qs where
    der: "derivation A (terms_pos (t |_ [a]) p) Cs qs \<and> last qs = q'"
    by (auto simp del: terms_pos.simps)
  {fix i assume "i < Suc (length Cs)"
    then have "derivation_ctxt (terms_pos (t |_ [a]) p @ [t]) (Cs @ [C])"
      using der C[symmetric] unfolding derivation_def
      by (cases "i = length Cs") (auto simp: nth_append_Cons)}
  note der_ctxt = this
  {fix i assume "i < Suc (length Cs)"
    then have "derivation_ctxt_st A (terms_pos (t |_ [a]) p @ [t]) (Cs @ [C]) (qs @ [q])"
      using der poss C res(2) last_conv_nth[of qs]
      by (cases "i = length Cs", auto 0 0 simp: derivation_def nth_append not_less less_Suc_eq) fastforce+}
  then show ?case using C poss res(1) der_ctxt der
    by (auto simp: derivation_def intro!: exI[of _ "Cs @ [C]"] exI[of _ "qs @ [q]"])
      (simp add: Cons.prems(2) nth_append_Cons)
qed

lemma derivation_ctxt_terms_pos_nt_empty:
  assumes "p \<in> poss t" and "derivation_ctxt (terms_pos t p) Cs" and "C \<in> set Cs"
  shows "C \<noteq> \<box>"
  using assms by (auto simp: in_set_conv_nth)
    (metis Suc_mono assms(2) ctxt_apply_term.simps(1) distinct_terms_pos lessI less_SucI less_irrefl_nat nth_eq_iff_index_eq)

lemma derivation_ctxt_terms_pos_sub_list_nt_empty:
  assumes "p \<in> poss t" and "derivation_ctxt (terms_pos t p) Cs"
    and "i < length Cs" and "j \<le> length Cs" and "i < j"
  shows "fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box> \<noteq> \<box>"
proof -
  have "\<exists> C. C \<in> set (take (j - i) (drop i Cs))"
    using assms(3-) not_le by fastforce
  then obtain C where w: "C \<in> set (take (j - i) (drop i Cs))" by blast
  then have "C \<noteq> \<box>"
    by auto (meson assms(1, 2) derivation_ctxt_terms_pos_nt_empty in_set_dropD in_set_takeD) 
  then show ?thesis by (auto simp: fold_ctxt_comp_nt_empty[OF w])
qed

lemma derivation_ctxt_comp_term:
  assumes "derivation_ctxt ts Cs"
    and "i < length Cs" and "j \<le> length Cs" and "i < j"
  shows "(fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box>)\<langle>ts ! i\<rangle> = ts ! j"
  using assms
proof (induct "j - i" arbitrary: j i)
  case (Suc x)
  then obtain n where j [simp]: "j = Suc n" by (meson lessE)
  then have r: "x = n - i" "Suc n - i = 1 + (n - i)" using Suc(2, 6) by linarith+
  then show ?case using Suc(1)[OF r(1)] Suc(2-) unfolding j r(2) take_add[of "n - i" 1]
    by (cases "i = n") (auto simp: take_Suc_conv_app_nth)
qed auto

lemma derivation_ctxt_comp_states:
  assumes "derivation_ctxt_st A ts Cs qs"
    and "i < length Cs" and "j \<le> length Cs" and "i < j"
  shows "qs ! j |\<in>| ta_der A (fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box>)\<langle>Var (qs ! i)\<rangle>"
  using assms
proof (induct "j - i" arbitrary: j i)
  case (Suc x)
  then obtain n where j [simp]: "j = Suc n" by (meson lessE)
  then have r: "x = n - i" "Suc n - i = 1 + (n - i)" using Suc(2, 6) by linarith+  
  then show ?case using Suc(1)[OF r(1)] Suc(2-) unfolding j r(2) take_add[of "n - i" 1]
    by (cases "i = n") (auto simp: take_Suc_conv_app_nth ta_der_ctxt)
qed auto

lemma terms_pos_ground:
  assumes "ground t" and "p \<in> poss t"
  shows "\<forall> s \<in> set (terms_pos t p). ground s"
  using terms_pos_subterm[OF assms(2)] subterm_eq_pres_ground[OF assms(1)] by simp


lemma list_card_smaller_contains_eq_elemens:
  assumes "length qs = n" and "card (set qs) < n"
  shows "\<exists> i < length qs. \<exists> j < length qs. i < j \<and> qs ! i = qs ! j"
  using assms by auto (metis distinct_card distinct_conv_nth linorder_neqE_nat) 

lemma length_remdups_less_eq:
  assumes "set xs \<subseteq> set ys"
  shows "length (remdups xs) \<le> length (remdups ys)" using assms
  by (auto simp: length_remdups_card_conv card_mono)

(* Main lemma *)

lemma pigeonhole_tree_automata:
  assumes "fcard (\<Q> A) < depth t" and "q |\<in>| ta_der A t" and "ground t"
  shows "\<exists> C C2 v p. C2 \<noteq> \<box> \<and> C\<langle>C2\<langle>v\<rangle>\<rangle> = t \<and> p |\<in>| ta_der A v \<and>
     p |\<in>| ta_der A C2\<langle>Var p\<rangle> \<and> q |\<in>| ta_der A C\<langle>Var p\<rangle>"
proof -
  obtain p n where p: "p \<in> poss t"  "depth t = n" and
    card: "fcard (\<Q> A) < n" "length (terms_pos t p) = (n + 1)"
    using assms(1) term_chain_depth by blast
  from ta_der_derivation_chain_terms_pos_exist[OF p(1) assms(2)] obtain Cs qs where
    derivation: "derivation A (terms_pos t p) Cs qs \<and> last qs = q" by blast
  then have d_ctxt: "derivation_ctxt_st A (terms_pos t p) Cs qs" "derivation_ctxt (terms_pos t p) Cs"
    by (auto simp: derivation_def)
  then have l: "length Cs = length qs - 1" by (auto simp: derivation_def)
  from derivation have sub: "fset_of_list qs |\<subseteq>| \<Q> A" "length qs = length (terms_pos t p)"
    unfolding derivation_def
    using ta_der_states[of A "t |_ i" for i] terms_pos_ground[OF assms(3) p(1)]
    by auto (metis derivation derivation_def gterm_of_term_inv gterm_ta_der_states in_fset_conv_nth nth_mem)
  then have "\<exists> i < length (butlast qs). \<exists> j < length (butlast qs). i < j \<and> (butlast qs) ! i = (butlast qs) ! j"
    using card(1, 2) assms(1) fcard_mono[OF sub(1)] length_remdups_less_eq[of "butlast qs" qs]
    by (intro list_card_smaller_contains_eq_elemens[of "butlast qs" n])
       (auto simp: card_set fcard_fset in_set_butlastD subsetI
                 intro!: le_less_trans[of "length (remdups (butlast qs))" "fcard (\<Q> A)" "length p"])
  then obtain i j where len: "i < length Cs" "j < length Cs" and less: "i < j" and st: "qs ! i = qs ! j"
    unfolding l length_butlast by (auto simp: nth_butlast)
  then have gt_0: "0 < length Cs" and gt_j: "0 < j" using len less less_trans by auto
  have "fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box> \<noteq> \<box>"
    using derivation_ctxt_terms_pos_sub_list_nt_empty[OF p(1) d_ctxt(2) len(1) order.strict_implies_order[OF len(2)] less] .
  moreover have "(fold (\<circ>\<^sub>c) (take (length Cs - j) (drop j Cs)) \<box>)\<langle>terms_pos t p ! j\<rangle> = terms_pos t p ! length Cs"
    using derivation_ctxt_comp_term[OF d_ctxt(2) len(2) _ len(2)] len(2) by auto
  moreover have "(fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box>)\<langle>terms_pos t p ! i\<rangle> = terms_pos t p ! j"
    using derivation_ctxt_comp_term[OF d_ctxt(2) len(1) _ less] len(2) by auto
  moreover have "qs ! j |\<in>| ta_der A (terms_pos t p ! i)" using derivation len
    by (auto simp: derivation_def st[symmetric])
  moreover have "qs ! j |\<in>| ta_der A (fold (\<circ>\<^sub>c) (take (j - i) (drop i Cs)) \<box>)\<langle>Var (qs ! i)\<rangle>"
    using derivation_ctxt_comp_states[OF d_ctxt(1) len(1) _ less] len(2) st by simp
  moreover have "q |\<in>| ta_der A (fold (\<circ>\<^sub>c) (take (length Cs - j) (drop j Cs)) \<box>)\<langle>Var (qs ! j)\<rangle>"
    using derivation_ctxt_comp_states[OF d_ctxt(1) len(2) _ len(2)] conjunct2[OF derivation]
    by (auto simp: l sub(2)) (metis Suc_inject Zero_not_Suc d_ctxt(1) l last_conv_nth list.size(3) terms_pos_length)
  ultimately show ?thesis using st d_ctxt(1) by (metis Suc_inject terms_pos_last terms_pos_length)
qed

end