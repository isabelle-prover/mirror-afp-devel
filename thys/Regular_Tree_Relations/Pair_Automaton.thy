theory Pair_Automaton
  imports Tree_Automata_Complement GTT_Compose
begin

subsection \<open>Pair automaton and anchored GTTs\<close>

definition pair_at_lang :: "('q, 'f) gtt \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> 'f gterm rel" where
  "pair_at_lang \<G> Q = {(s, t) | s t p q. q |\<in>| gta_der (fst \<G>) s \<and> p |\<in>| gta_der (snd \<G>) t \<and> (q, p) |\<in>| Q}"

lemma pair_at_lang_restr_states:
  "pair_at_lang \<G> Q = pair_at_lang \<G> (Q |\<inter>| (\<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)))"
  by (auto simp: pair_at_lang_def gta_der_def) (meson gterm_ta_der_states) 

lemma pair_at_langE:
  assumes "(s, t) \<in> pair_at_lang \<G> Q"
  obtains q p where "(q, p) |\<in>| Q" and "q |\<in>| gta_der (fst \<G>) s" and "p |\<in>| gta_der (snd \<G>) t"
  using assms by (auto simp: pair_at_lang_def)

lemma pair_at_langI:
  assumes "q |\<in>| gta_der (fst \<G>) s" "p |\<in>| gta_der (snd \<G>) t" "(q, p) |\<in>| Q"
  shows "(s, t) \<in> pair_at_lang \<G> Q"
  using assms by (auto simp: pair_at_lang_def)

lemma pair_at_lang_fun_states:
  assumes "finj_on f (\<Q> (fst \<G>))" and "finj_on g (\<Q> (snd \<G>))"
    and "Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)"
  shows "pair_at_lang \<G> Q = pair_at_lang (map_prod (fmap_states_ta f) (fmap_states_ta g) \<G>) (map_prod f g |`| Q)"
    (is "?LS = ?RS")
proof
  {fix s t assume "(s, t) \<in> ?LS"
    then have "(s, t) \<in> ?RS" using ta_der_fmap_states_ta_mono[of f "fst \<G>" s]
      using ta_der_fmap_states_ta_mono[of g "snd \<G>" t]
      by (force simp: gta_der_def map_prod_def image_iff  elim!: pair_at_langE split: prod.split intro!: pair_at_langI)}
  then show "?LS \<subseteq> ?RS" by auto
next
  {fix s t assume "(s, t) \<in> ?RS"
    then obtain p q where rs: "p |\<in>| ta_der (fst \<G>) (term_of_gterm s)" "f p |\<in>| ta_der (fmap_states_ta f (fst \<G>)) (term_of_gterm s)" and
      ts: "q |\<in>| ta_der (snd \<G>) (term_of_gterm t)" "g q |\<in>| ta_der (fmap_states_ta g (snd \<G>)) (term_of_gterm t)" and
      st: "(f p, g q) |\<in>| (map_prod f g |`| Q)" using assms ta_der_fmap_states_inv[of f "fst \<G>" _ s]
      using ta_der_fmap_states_inv[of g "snd \<G>" _ t]
      by (auto simp: gta_der_def adapt_vars_term_of_gterm elim!: pair_at_langE)
        (metis (no_types, opaque_lifting) f_the_finv_into_f fimage.rep_eq fmap_prod_fimageI
          fmap_states gterm_ta_der_states)
    then have "p |\<in>| \<Q> (fst \<G>)" "q |\<in>| \<Q> (snd \<G>)" by auto
    then have "(p, q) |\<in>| Q" using assms st unfolding fimage_iff fBex_def
      by (auto dest!: fsubsetD simp: finj_on_eq_iff)
    then have "(s, t) \<in> ?LS" using st rs(1) ts(1) by (auto simp: gta_der_def intro!: pair_at_langI)}
  then show "?RS \<subseteq> ?LS" by auto
qed

lemma converse_pair_at_lang:
  "(pair_at_lang \<G> Q)\<inverse> = pair_at_lang (prod.swap \<G>) (Q|\<inverse>|)"
  by (auto simp: pair_at_lang_def)

lemma pair_at_agtt:
  "agtt_lang \<G> = pair_at_lang \<G> (fId_on (gtt_interface \<G>))"
  by (auto simp: agtt_lang_def gtt_interface_def pair_at_lang_def gtt_states_def gta_der_def fId_on_iff)

definition \<Delta>_eps_pair where
  "\<Delta>_eps_pair \<G>\<^sub>1 Q\<^sub>1 \<G>\<^sub>2 Q\<^sub>2 \<equiv>  Q\<^sub>1 |O| \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2) |O| Q\<^sub>2"

lemma pair_comp_sound1:
  assumes "(s, t) \<in> pair_at_lang \<G>\<^sub>1 Q\<^sub>1"
    and "(t, u) \<in> pair_at_lang \<G>\<^sub>2 Q\<^sub>2"
  shows "(s, u) \<in> pair_at_lang (fst \<G>\<^sub>1, snd \<G>\<^sub>2) (\<Delta>_eps_pair \<G>\<^sub>1 Q\<^sub>1 \<G>\<^sub>2 Q\<^sub>2)"
proof -
  from pair_at_langE assms obtain p q  q' r where
    wit: "(p, q) |\<in>| Q\<^sub>1" "p |\<in>| gta_der (fst \<G>\<^sub>1) s" "q |\<in>| gta_der (snd \<G>\<^sub>1) t"
    "(q', r) |\<in>| Q\<^sub>2" "q' |\<in>| gta_der (fst \<G>\<^sub>2) t" "r |\<in>| gta_der (snd \<G>\<^sub>2) u"
      by metis
  from wit(3, 5) have "(q, q') |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2)"
    by (auto simp: \<Delta>\<^sub>\<epsilon>_def' gta_der_def intro!: exI[of _ "term_of_gterm t"])
  then have "(p, r) |\<in>| \<Delta>_eps_pair \<G>\<^sub>1 Q\<^sub>1 \<G>\<^sub>2 Q\<^sub>2" using wit(1, 4)
    by (auto simp: \<Delta>_eps_pair_def)
  then show ?thesis using wit(2, 6) unfolding pair_at_lang_def
    by auto
qed

lemma pair_comp_sound2:
  assumes "(s, u) \<in>  pair_at_lang (fst \<G>\<^sub>1, snd \<G>\<^sub>2) (\<Delta>_eps_pair \<G>\<^sub>1 Q\<^sub>1 \<G>\<^sub>2 Q\<^sub>2)"
  shows "\<exists> t. (s, t) \<in> pair_at_lang \<G>\<^sub>1 Q\<^sub>1 \<and> (t, u) \<in> pair_at_lang \<G>\<^sub>2 Q\<^sub>2"
  using assms unfolding pair_at_lang_def \<Delta>_eps_pair_def
  by (auto simp: \<Delta>\<^sub>\<epsilon>_def' gta_der_def) (metis gterm_of_term_inv)

lemma pair_comp_sound:
  "pair_at_lang \<G>\<^sub>1 Q\<^sub>1 O pair_at_lang \<G>\<^sub>2 Q\<^sub>2 = pair_at_lang (fst \<G>\<^sub>1, snd \<G>\<^sub>2) (\<Delta>_eps_pair \<G>\<^sub>1 Q\<^sub>1 \<G>\<^sub>2 Q\<^sub>2)"
  by (auto simp: pair_comp_sound1 pair_comp_sound2 relcomp.simps)

inductive_set \<Delta>_Atrans_set :: "('q \<times> 'q) fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) set" for Q \<A> \<B> where
  base [simp]: "(p, q) |\<in>| Q \<Longrightarrow> (p, q) \<in> \<Delta>_Atrans_set Q \<A> \<B>"
| step [intro]: "(p, q) \<in> \<Delta>_Atrans_set Q \<A> \<B> \<Longrightarrow> (q, r) |\<in>| \<Delta>\<^sub>\<epsilon> \<B> \<A> \<Longrightarrow>
     (r, v) \<in> \<Delta>_Atrans_set Q \<A> \<B> \<Longrightarrow> (p, v) \<in> \<Delta>_Atrans_set Q \<A> \<B>"

lemma \<Delta>_Atrans_set_states:
  "(p, q) \<in> \<Delta>_Atrans_set Q \<A> \<B> \<Longrightarrow> (p, q) \<in> fset ((fst |`| Q |\<union>| \<Q> \<A>) |\<times>| (snd |`| Q |\<union>| \<Q> \<B>))"
  by (induct rule: \<Delta>_Atrans_set.induct) (auto simp: image_iff intro!: bexI)

lemma finite_\<Delta>_Atrans_set: "finite (\<Delta>_Atrans_set Q \<A> \<B>)"
proof -
  have "\<Delta>_Atrans_set Q \<A> \<B> \<subseteq> fset ((fst |`| Q |\<union>| \<Q> \<A>) |\<times>| (snd |`| Q |\<union>| \<Q> \<B>))"
    using \<Delta>_Atrans_set_states
    by (metis subrelI)
  from finite_subset[OF this] show ?thesis by simp
qed

context
includes fset.lifting
begin
lift_definition \<Delta>_Atrans ::  "('q \<times> 'q) fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) fset" is \<Delta>_Atrans_set
  by (simp add: finite_\<Delta>_Atrans_set)

lemmas \<Delta>_Atrans_base [simp] = \<Delta>_Atrans_set.base [Transfer.transferred]
lemmas \<Delta>_Atrans_step [intro] = \<Delta>_Atrans_set.step [Transfer.transferred]
lemmas \<Delta>_Atrans_cases = \<Delta>_Atrans_set.cases[Transfer.transferred]
lemmas \<Delta>_Atrans_induct [consumes 1, case_names base step] = \<Delta>_Atrans_set.induct[Transfer.transferred]
end

abbreviation "\<Delta>_Atrans_gtt \<G> Q \<equiv> \<Delta>_Atrans Q (fst \<G>) (snd \<G>)"

lemma pair_trancl_sound1:
  assumes "(s, t) \<in> (pair_at_lang \<G> Q)\<^sup>+"
  shows "\<exists> q p. p |\<in>| gta_der (fst \<G>) s \<and> q |\<in>| gta_der (snd \<G>) t \<and> (p, q) |\<in>| \<Delta>_Atrans_gtt \<G> Q"
  using assms
proof (induct)
  case (step t v)
  obtain p q r r' where reach_t: "r |\<in>| gta_der (fst \<G>) t" "q |\<in>| gta_der (snd \<G>) t" and
    reach: "p |\<in>| gta_der (fst \<G>) s" "r' |\<in>| gta_der (snd \<G>) v" and
    st: "(p, q) |\<in>| \<Delta>_Atrans_gtt \<G> Q"  "(r, r') |\<in>| Q" using step(2, 3)
    by (auto simp: pair_at_lang_def)
  from reach_t have "(q, r) |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>) (fst \<G>)"
    by (auto simp: \<Delta>\<^sub>\<epsilon>_def' gta_der_def intro: ground_term_of_gterm)
  then have "(p, r') |\<in>| \<Delta>_Atrans_gtt \<G> Q" using st by auto
  then show ?case using reach reach_t
    by (auto simp: pair_at_lang_def gta_der_def \<Delta>\<^sub>\<epsilon>_def' intro: ground_term_of_gterm)
qed (auto simp: pair_at_lang_def intro: \<Delta>_Atrans_base)

lemma pair_trancl_sound2:
  assumes "(p, q) |\<in>| \<Delta>_Atrans_gtt \<G> Q"
    and "p |\<in>| gta_der (fst \<G>) s" "q |\<in>| gta_der (snd \<G>) t"
  shows "(s, t) \<in> (pair_at_lang \<G> Q)\<^sup>+" using assms
proof (induct arbitrary: s t rule:\<Delta>_Atrans_induct)
  case (step p q r v)
  from step(2)[OF step(6)] step(5)[OF _ step(7)] step(3)
  show ?case by (auto simp: gta_der_def \<Delta>\<^sub>\<epsilon>_def' intro!: ground_term_of_gterm)
      (metis gterm_of_term_inv trancl_trans)
qed (auto simp: pair_at_lang_def)

lemma pair_trancl_sound:
  "(pair_at_lang \<G> Q)\<^sup>+ = pair_at_lang \<G> (\<Delta>_Atrans_gtt \<G> Q)"
  by (auto simp: pair_trancl_sound2 dest: pair_trancl_sound1 elim: pair_at_langE intro: pair_at_langI)

abbreviation "fst_pair_cl \<A> Q \<equiv> TA (rules \<A>) (eps \<A> |\<union>| (fId_on (\<Q> \<A>) |O| Q))"
definition pair_at_to_agtt :: "('q, 'f) gtt \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> ('q, 'f) gtt" where
  "pair_at_to_agtt \<G> Q = (fst_pair_cl (fst \<G>) Q , TA (rules (snd \<G>)) (eps (snd \<G>)))"

lemma fst_pair_cl_eps:
  assumes "(p, q) |\<in>| (eps (fst_pair_cl \<A> Q))|\<^sup>+|"
    and "\<Q> \<A> |\<inter>| snd |`| Q = {||}"
  shows "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<or> (\<exists> r. (p = r \<or> (p, r) |\<in>| (eps \<A>)|\<^sup>+|) \<and> (r, q) |\<in>| Q)" using assms
proof (induct rule: ftrancl_induct)
  case (Step p q r)
  then have y: "q |\<in>| \<Q> \<A>" by (auto simp add: eps_trancl_statesD eps_statesD)
  have [simp]: "(p, q) |\<in>| Q \<Longrightarrow> q |\<in>| snd |`| Q" for p q by (auto simp: fimage_iff) force 
  then show ?case using Step y
    by auto (simp add: ftrancl_into_trancl)
qed auto

lemma fst_pair_cl_res_aux:
  assumes "\<Q> \<A> |\<inter>| snd |`| Q = {||}"
    and "q |\<in>| ta_der (fst_pair_cl \<A> Q) (term_of_gterm t)"
  shows "\<exists> p. p |\<in>| ta_der \<A> (term_of_gterm t) \<and> (q |\<notin>| \<Q> \<A> \<longrightarrow> (p, q) |\<in>| Q) \<and> (q |\<in>| \<Q> \<A> \<longrightarrow> p = q)" using assms
proof (induct t arbitrary: q)
  case (GFun f ts)
  then obtain qs q' where rule: "TA_rule f qs q' |\<in>| rules \<A>" "length qs = length ts" and
    eps: "q' = q \<or> (q', q) |\<in>| (eps (fst_pair_cl \<A> Q))|\<^sup>+|" and
    reach: "\<forall> i < length ts. qs ! i |\<in>| ta_der (fst_pair_cl \<A> Q) (term_of_gterm (ts ! i))"
    by auto
  {fix i assume ass: "i < length ts" then have st: "qs ! i |\<in>| \<Q> \<A>" using rule
      by (auto simp: rule_statesD)
    then have "qs ! i |\<notin>| snd |`| Q" using GFun(2) by auto
    then have "qs ! i |\<in>| ta_der \<A> (term_of_gterm (ts ! i))" using reach st ass
      using fst_pair_cl_eps[OF _ GFun(2)] GFun(1)[OF nth_mem[OF ass] GFun(2), of "qs ! i"]
      by blast} note IH = this
  show ?case
  proof (cases "q' = q")
    case True
    then show ?thesis using rule reach IH
      by (auto dest: rule_statesD intro!: exI[of _ q'] exI[of _ qs])
  next
    case False note nt_eq = this
    then have eps: "(q', q) |\<in>| (eps (fst_pair_cl \<A> Q))|\<^sup>+|" using eps by simp
    from fst_pair_cl_eps[OF this assms(1)] show ?thesis
      using False rule IH
    proof (cases "q |\<notin>| \<Q> \<A>")
      case True
      from fst_pair_cl_eps[OF eps assms(1)] obtain r where
         "q' = r \<or> (q', r) |\<in>| (eps \<A>)|\<^sup>+|" "(r, q) |\<in>| Q" using True
        by (auto simp: eps_trancl_statesD)
      then show ?thesis using nt_eq rule IH True
        by (auto simp: fimage_iff eps_trancl_statesD)
    next
      case False
      from fst_pair_cl_eps[OF eps assms(1)] False assms(1)
      have "(q', q) |\<in>| (eps \<A>)|\<^sup>+|"
        by (auto simp: fimage_iff) (metis fempty_iff fimage_eqI finterI snd_conv)+
      then show ?thesis using IH rule
        by (intro exI[of _ q]) (auto simp: eps_trancl_statesD)
    qed
  qed
qed

lemma restr_distjoing:
  assumes "Q |\<subseteq>| \<Q> \<A> |\<times>| \<Q> \<BB>"
    and "\<Q> \<A> |\<inter>| \<Q> \<BB> = {||}"
  shows "\<Q> \<A> |\<inter>| snd |`| Q = {||}"
  using assms by auto

lemma pair_at_agtt_conv:
  assumes "Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)" and "\<Q> (fst \<G>) |\<inter>| \<Q> (snd \<G>) = {||}"
  shows "pair_at_lang \<G> Q = agtt_lang (pair_at_to_agtt \<G> Q)" (is "?LS = ?RS")
proof
  let ?TA = "fst_pair_cl (fst \<G>) Q"
  {fix s t assume ls: "(s, t) \<in> ?LS"
    then obtain q p where w: "(q, p) |\<in>| Q" "q |\<in>| gta_der (fst \<G>) s" "p |\<in>| gta_der (snd \<G>) t"
      by (auto elim: pair_at_langE)
    from w(2) have "q |\<in>| gta_der ?TA s" "q |\<in>| \<Q> (fst \<G>)"
      using ta_der_mono'[of "fst \<G>" ?TA "term_of_gterm s"]
      by (auto simp add: fin_mono ta_subset_def gta_der_def in_mono)
    then have "(s, t) \<in> ?RS" using w(1, 3)
      by (auto simp: pair_at_to_agtt_def agtt_lang_def gta_der_def ta_der_eps intro!: exI[of _ p])
         (metis fId_onI frelcompI funionI2 ta.sel(2) ta_der_eps)}
  then show "?LS \<subseteq> ?RS" by auto
next
  {fix s t assume ls: "(s, t) \<in> ?RS"
    then obtain q where w: "q |\<in>| ta_der (fst_pair_cl (fst \<G>) Q) (term_of_gterm s)"
      "q |\<in>| ta_der (snd \<G>) (term_of_gterm t)"
      by (auto simp: agtt_lang_def pair_at_to_agtt_def gta_der_def)
    from w(2) have "q |\<in>| \<Q> (snd \<G>)" "q |\<notin>| \<Q> (fst \<G>)" using assms(2)
      by auto
    from fst_pair_cl_res_aux[OF restr_distjoing[OF assms] w(1)] this w(2)
    have "(s, t) \<in> ?LS" by (auto simp: agtt_lang_def pair_at_to_agtt_def gta_der_def intro: pair_at_langI)}
  then show "?RS \<subseteq> ?LS" by auto
qed

definition pair_at_to_agtt' where
  "pair_at_to_agtt' \<G> Q = (let \<A> = fmap_states_ta Inl (fst \<G>) in
    let \<B> = fmap_states_ta Inr (snd \<G>) in
    let Q' = Q |\<inter>| (\<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)) in
    pair_at_to_agtt (\<A>, \<B>) (map_prod Inl Inr |`| Q'))"

lemma pair_at_agtt_cost:
  "pair_at_lang \<G> Q = agtt_lang (pair_at_to_agtt' \<G> Q)"
proof -
  let ?G = "(fmap_states_ta CInl (fst \<G>), fmap_states_ta CInr (snd \<G>))"
  let ?Q = "(Q |\<inter>| (\<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)))"
  let ?Q' = "map_prod CInl CInr |`| ?Q"
  have *: "pair_at_lang \<G> Q = pair_at_lang \<G> ?Q"
    using pair_at_lang_restr_states by blast
  have "pair_at_lang \<G> ?Q = pair_at_lang (map_prod (fmap_states_ta CInl) (fmap_states_ta CInr) \<G>) (map_prod CInl CInr |`| ?Q)"
    by (intro pair_at_lang_fun_states[where ?\<G> = \<G> and ?Q = ?Q and ?f = CInl and ?g = CInr])
       (auto simp: finj_CInl_CInr)
  then have **:"pair_at_lang \<G> ?Q = pair_at_lang ?G ?Q'" by (simp add: map_prod_simp')
  have "pair_at_lang ?G ?Q' = agtt_lang (pair_at_to_agtt ?G ?Q')"
    by (intro pair_at_agtt_conv[where ?\<G> = ?G]) auto
  then show ?thesis unfolding * ** pair_at_to_agtt'_def Let_def
    by simp
qed

lemma \<Delta>_Atrans_states_stable:
  assumes "Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)"
  shows "\<Delta>_Atrans_gtt \<G> Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)"
proof
  fix s assume ass: "s |\<in>| \<Delta>_Atrans_gtt \<G> Q"
  then obtain t u where s: "s = (t, u)" by (cases s) blast
  show "s |\<in>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)" using ass assms unfolding s
    by (induct rule: \<Delta>_Atrans_induct) auto
qed

lemma \<Delta>_Atrans_map_prod:
  assumes "finj_on f (\<Q> (fst \<G>))" and "finj_on g (\<Q> (snd \<G>))"
    and "Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)"
  shows "map_prod f g |`| (\<Delta>_Atrans_gtt \<G> Q) = \<Delta>_Atrans_gtt (map_prod (fmap_states_ta f) (fmap_states_ta g) \<G>) (map_prod f g |`| Q)"
    (is "?LS = ?RS")
proof -
  {fix p q assume "(p, q) |\<in>| \<Delta>_Atrans_gtt \<G> Q"
    then have "(f p, g q) |\<in>| ?RS" using assms
    proof (induct rule: \<Delta>_Atrans_induct)
      case (step p q r v)
      from step(3, 6, 7) have "(g q, f r) |\<in>| \<Delta>\<^sub>\<epsilon> (fmap_states_ta g (snd \<G>)) (fmap_states_ta f (fst \<G>))"
        by (auto simp: \<Delta>\<^sub>\<epsilon>_def' intro!: ground_term_of_gterm)
           (metis ground_term_of_gterm ground_term_to_gtermD ta_der_to_fmap_states_der)
      then show ?case using step by auto
    qed (auto simp add: map_prod_imageI)}
  moreover
  {fix p q assume "(p, q) |\<in>| ?RS"
    then have "(p, q) |\<in>| ?LS" using assms
    proof (induct rule: \<Delta>_Atrans_induct)
      case (step p q r v)
      let ?f = "the_finv_into (\<Q> (fst \<G>)) f" let ?g = "the_finv_into (\<Q> (snd \<G>)) g"
      have sub: "\<Delta>\<^sub>\<epsilon> (snd \<G>) (fst \<G>) |\<subseteq>| \<Q> (snd \<G>) |\<times>| \<Q> (fst \<G>)"
        using \<Delta>\<^sub>\<epsilon>_statesD(1, 2) by fastforce
      have s_e: "(?f p, ?g q) |\<in>| \<Delta>_Atrans_gtt \<G> Q" "(?f r, ?g v) |\<in>| \<Delta>_Atrans_gtt \<G> Q"
        using step assms(1, 2) fsubsetD[OF \<Delta>_Atrans_states_stable[OF assms(3)]]
        using finj_on_eq_iff[OF assms(1)] finj_on_eq_iff
        using the_finv_into_f_f[OF assms(1)] the_finv_into_f_f[OF assms(2)]
        by auto
      from step(3) have "(?g q, ?f r) |\<in>| \<Delta>\<^sub>\<epsilon> (snd \<G>) (fst \<G>)"
        using step(6-) sub
        using ta_der_fmap_states_conv[OF assms(1)] ta_der_fmap_states_conv[OF assms(2)]
        using the_finv_into_f_f[OF assms(1)] the_finv_into_f_f[OF assms(2)]
        by (auto simp: \<Delta>\<^sub>\<epsilon>_fmember fimage_iff fBex_def)
           (metis ground_term_of_gterm ground_term_to_gtermD ta_der_fmap_states_inv)
      then have "(q, r) |\<in>| map_prod g f |`| \<Delta>\<^sub>\<epsilon> (snd \<G>) (fst \<G>)" using step
        using the_finv_into_f_f[OF assms(1)] the_finv_into_f_f[OF assms(2)] sub
        by (smt (verit, ccfv_threshold) \<Delta>\<^sub>\<epsilon>_statesD(1) \<Delta>\<^sub>\<epsilon>_statesD(2) f_the_finv_into_f fimage.rep_eq
            fmap_states fst_map_prod map_prod_imageI snd_map_prod)
      then show ?case using s_e assms(1, 2) s_e
        using fsubsetD[OF sub]
        using fsubsetD[OF \<Delta>_Atrans_states_stable[OF assms(3)]]
        using \<Delta>_Atrans_step[of "?f p" "?g q" Q "fst \<G>" "snd \<G>" "?f r" "?g v"]
        using the_finv_into_f_f[OF assms(1)] the_finv_into_f_f[OF assms(2)]
        using step.hyps(2) step.hyps(5) step.prems(3) by force
    qed auto}
  ultimately show ?thesis by auto
qed

\<comment> \<open>Section: Pair Automaton is closed under Determinization\<close>

definition Q_pow where
  "Q_pow Q \<S>\<^sub>1 \<S>\<^sub>2 =
    {|(Wrapp X, Wrapp Y) | X Y p q. X |\<in>| fPow \<S>\<^sub>1 \<and> Y |\<in>| fPow \<S>\<^sub>2 \<and> p |\<in>| X \<and> q |\<in>| Y \<and> (p, q) |\<in>| Q|}"

lemma Q_pow_fmember:
  "(X, Y) |\<in>| Q_pow Q \<S>\<^sub>1 \<S>\<^sub>2 \<longleftrightarrow> (\<exists> p q. ex X |\<in>| fPow \<S>\<^sub>1 \<and> ex Y |\<in>| fPow \<S>\<^sub>2 \<and> p |\<in>| ex X \<and> q |\<in>| ex Y \<and> (p, q) |\<in>| Q)"
proof -
  let ?S = "{(Wrapp X, Wrapp Y) | X Y p q. X |\<in>| fPow \<S>\<^sub>1 \<and> Y |\<in>| fPow \<S>\<^sub>2 \<and> p |\<in>| X \<and> q |\<in>| Y \<and> (p, q) |\<in>| Q}" 
  have "?S \<subseteq> map_prod Wrapp Wrapp ` fset (fPow \<S>\<^sub>1 |\<times>| fPow \<S>\<^sub>2)" by auto
  from finite_subset[OF this] show ?thesis unfolding Q_pow_def
    apply auto apply blast
    by (meson FSet_Lex_Wrapper.exhaust_sel)
qed

lemma pair_automaton_det_lang_sound_complete:
  "pair_at_lang \<G> Q = pair_at_lang (map_both ps_ta \<G>) (Q_pow Q (\<Q> (fst \<G>)) (\<Q> (snd \<G>)))" (is "?LS = ?RS")
proof -
  {fix s t assume "(s, t) \<in> ?LS"
    then obtain  p q where
      res : "p |\<in>| ta_der (fst \<G>) (term_of_gterm s)"
      "q |\<in>| ta_der (snd \<G>) (term_of_gterm t)" "(p, q) |\<in>| Q"
      by (auto simp: pair_at_lang_def gta_der_def)
    from ps_rules_complete[OF this(1)] ps_rules_complete[OF this(2)] this(3)
    have "(s, t) \<in> ?RS" using fPow_iff ps_ta_states'
      apply (auto simp: pair_at_lang_def gta_der_def Q_pow_fmember)
      by (smt (verit, best) dual_order.trans ground_ta_der_states ground_term_of_gterm ps_rules_sound)}
  moreover
  {fix s t assume "(s, t) \<in> ?RS" then have "(s, t) \<in> ?LS"
      using ps_rules_sound
      by (auto simp: pair_at_lang_def gta_der_def ps_ta_def Let_def Q_pow_fmember) blast}
  ultimately show ?thesis by auto
qed

lemma pair_automaton_complement_sound_complete:
  assumes "partially_completely_defined_on \<A> \<F>" and "partially_completely_defined_on \<B> \<F>"
    and "ta_det \<A>" and "ta_det \<B>"
  shows "pair_at_lang (\<A>, \<B>) (\<Q> \<A> |\<times>| \<Q> \<B> |-| Q) = gterms (fset \<F>) \<times> gterms (fset \<F>) - pair_at_lang (\<A>, \<B>) Q"
  using assms unfolding partially_completely_defined_on_def pair_at_lang_def
  apply (auto simp: gta_der_def)
  apply (metis ta_detE)
  apply fastforce
  done

end
