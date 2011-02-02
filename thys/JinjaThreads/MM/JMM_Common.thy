(*  Title:      JinjaThreads/MM/JMM_Common.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM Instantiation with Jinja -- common parts} *}

theory JMM_Common imports
  JMM_Type
  SC_Completion
  "../Framework/FWInitFinLift"
begin

lemma distinct_filterD:
  "\<lbrakk> distinct (filter P xs); n < length xs; m < length xs; P x; xs ! n = x; xs ! m = x \<rbrakk> \<Longrightarrow> m = n"
using ldistinct_lfilterD[of P "llist_of xs" n m x] by simp

context heap begin

lemma init_fin_lift_state_start_state:
  "init_fin_lift_state s (start_state f P C M vs) = start_state (\<lambda>C M Ts T meth vs. (s, f C M Ts T meth vs)) P C M vs"
by(simp add: start_state_def init_fin_lift_state_def split_beta fun_eq_iff)

end

section {* JMM traces for Jinja semantics *}

context \<tau>multithreaded begin

inductive_set \<E> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> 'o) llist set"
  for \<sigma> :: "('l,'t,'x,'m,'w) state"
where
  "mthr.\<tau>Runs \<sigma> E'
  \<Longrightarrow> lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) \<in> \<E> \<sigma>"

lemma actions_\<E>E_aux:
  fixes \<sigma> E'
  defines "E == lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
  assumes mthr: "mthr.\<tau>Runs \<sigma> E'"
  and a: "Fin a < llength E"
  obtains m n t ta
  where "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "Fin m < tlength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "tnth E' m = (t, ta)"
proof -
  from lnth_lconcat_conv[OF a[unfolded E_def], folded E_def]
  obtain m n
    where "lnth E a = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) m) n"
    and "Fin n < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) m)"
    and "Fin m < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and "Fin a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin n"
    by blast
  moreover
  obtain t ta where "tnth E' m = (t, ta)" by(cases "tnth E' m")
  ultimately have E_a: "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
    and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and m: "Fin m < tlength E'"
    and a: "Fin a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin n"
    by(simp_all add: lnth_llist_of)
  note a
  also have "(\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) = 
            setsum (Fin \<circ> (\<lambda>i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) {..<m}"
    using m by(simp add: less_trans[where y="Fin m"] split_beta)
  also have "\<dots> = Fin (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
    by(subst setsum_hom)(simp_all add: zero_inat_def)
  finally have a: "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n" by simp
  with E_a n m show thesis using `tnth E' m = (t, ta)` by(rule that)
qed

lemma actions_\<E>E:
  assumes E: "E \<in> \<E> \<sigma>"
  and a: "Fin a < llength E"
  obtains E' m n t ta
  where "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
  and "mthr.\<tau>Runs \<sigma> E'"
  and "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "Fin m < tlength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "tnth E' m = (t, ta)"
proof -
  from E obtain E' ws
    where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and "mthr.\<tau>Runs \<sigma> E'" by(rule \<E>.cases) blast
  from `mthr.\<tau>Runs \<sigma> E'` a[unfolded E]
  show ?thesis
    by(rule actions_\<E>E_aux)(fold E, rule that[OF E `mthr.\<tau>Runs \<sigma> E'`])
qed

end

context \<tau>multithreaded_wf begin

text {* Alternative characterisation for @{term "\<E>"} *}
lemma \<E>_conv_Runs:
  "\<E> \<sigma> = lconcat ` lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ` {E. mthr.Runs \<sigma> E}"
  (is "?lhs = ?rhs")
proof(intro equalityI subsetI)
  fix E
  assume "E \<in> ?lhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and \<tau>Runs: "mthr.\<tau>Runs \<sigma> E'" by(blast elim: \<E>.cases)
  obtain E'' where E': "E' = tmap (\<lambda>(tls, s', tl, s''). tl) (sum_case (\<lambda>(tls, s'). \<lfloor>s'\<rfloor>) Map.empty) E''"
    and \<tau>Runs': "mthr.\<tau>Runs_table2 \<sigma> E''"
    using \<tau>Runs by(rule mthr.\<tau>Runs_into_\<tau>Runs_table2)
  have "mthr.Runs \<sigma> (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) 
                                      (LCons (case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil)))"
    (is "mthr.Runs _ ?E'''")
    using \<tau>Runs' by(rule mthr.\<tau>Runs_table2_into_Runs)
  moreover 
  let ?tail = "\<lambda>E''. case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls"
  {
    have "E = lconcat (lfilter (\<lambda>xs. xs \<noteq> LNil) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))"
      unfolding E by(simp add: lconcat_lfilter_neq_LNil)
    also have "\<dots> = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E''))))"
      by(simp add: E' lfilter_lmap lmap_compose[symmetric] o_def split_def)
    also
    have "(lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')),
           lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil)))) \<in>
          {(lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')),
           lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))
          |E''. \<exists>\<sigma>. mthr.\<tau>Runs_table2 \<sigma> E''}" 
      (is "_ \<in> ?r")
      using \<tau>Runs' by blast
    hence "lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')) = 
          lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil)))"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain E'' \<sigma> 
        where q: "q = (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')), lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))"
        and \<tau>Runs': "mthr.\<tau>Runs_table2 \<sigma> E''"
        by blast
      show ?case
      proof(cases "fst q")
        case LNil
        hence "\<forall>(tls, s', (t, ta), s'') \<in> lset (llist_of_tllist E''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []"
          using q by(auto simp add: lfilter_empty_conv)
        hence "\<forall>(t, ta) \<in> lset (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []"
          by(cases "lfinite (llist_of_tllist E'')")(fastsimp simp add: lset_lappend_lfinite split_beta lset_lconcat_lfinite lappend_inf mthr.silent_move2_def dest: mthr.\<tau>Runs_table2_silentsD[OF \<tau>Runs'] mthr.\<tau>Runs_table2_terminal_silentsD[OF \<tau>Runs'] mthr.\<tau>Runs_table2_terminal_inf_stepD[OF \<tau>Runs'] m\<tau>move_silentD inf_step_silentD silent_moves2_silentD split: sum.split_asm)+
        hence "lfilter (\<lambda>(t, ta). obs_a ta \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))) = LNil"
          by(simp add: lfilter_empty_conv split_beta)
        thus ?thesis using LNil q by simp
      next
        case (LCons tl tls')
        then obtain tls s' s'' tlsstlss' where tls': "tls' = lmap (\<lambda>(tls, s', tta, s''). tta) tlsstlss'"
          and filter: "lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) (llist_of_tllist E'') = LCons (tls, s', tl, s'') tlsstlss'"
          using q by(fastsimp simp add: lmap_eq_LCons_conv)
        from lfilter_eq_LConsD[OF filter]
        obtain us vs where eq: "llist_of_tllist E'' = lappend us (LCons (tls, s', tl, s'') vs)"
          and fin: "lfinite us"
          and empty: "\<forall>(tls, s', (t, ta), s'')\<in>lset us. obs_a ta = []"
          and neq_empty: "obs_a (snd tl) \<noteq> []"
          and tlsstlss': "tlsstlss' = lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) vs"
          by(auto simp add: split_beta)
        from eq obtain E''' where E'': "E'' = lappendt us E'''" 
          and eq': "llist_of_tllist E''' = LCons (tls, s', tl, s'') vs"
          and terminal: "terminal E''' = terminal E''"
          unfolding llist_of_tllist_eq_lappend_conv by auto
        from \<tau>Runs' fin E'' obtain \<sigma>' where \<tau>Runs'': "mthr.\<tau>Runs_table2 \<sigma>' E'''"
          by(auto dest: mthr.\<tau>Runs_table2_lappendtD)
        then obtain \<sigma>'' E'''' where "mthr.\<tau>Runs_table2 \<sigma>'' E''''" "E''' = TCons (tls, s', tl, s'') E''''"
          using eq' by cases auto
        moreover from \<tau>Runs' E'' fin
        have "\<forall>(tls, s, tl, s')\<in>lset us. \<forall>(t, ta)\<in>set tls. ta = \<epsilon>"
          by(fastsimp dest: mthr.\<tau>Runs_table2_silentsD m\<tau>move_silentD simp add: mthr.silent_move2_def)
        hence "lfilter (\<lambda>(t, ta). obs_a ta \<noteq> []) (lconcat (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) us)) = LNil"
          using empty by(auto simp add: lfilter_empty_conv lset_lconcat_lfinite split_beta)
        moreover from \<tau>Runs'' eq' have "snd ` set tls \<subseteq> {\<epsilon>}"
          by(cases)(fastsimp dest: silent_moves2_silentD)+
        hence "[(t, ta)\<leftarrow>tls . obs_a ta \<noteq> []] = []"
          by(auto simp add: filter_empty_conv split_beta)
        ultimately have ?EqLCons
          using LCons q E'' fin tls' tlsstlss' filter eq' neq_empty
          by(fastsimp simp add: lmap_lappend_distrib lappend_assoc lfilter_lappend_lfinite split_beta simp del: split_paired_Ex)
        thus ?thesis ..
      qed
    qed
    also have "lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) \<dots> = lfilter (\<lambda>obs. obs \<noteq> LNil) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))"
      unfolding lfilter_lmap by(simp add: o_def split_def)
    finally have "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?E''')"
      by(simp add: lconcat_lfilter_neq_LNil) }
  ultimately show "E \<in> ?rhs" by blast
next
  fix E
  assume "E \<in> ?rhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) E')"
    and Runs: "mthr.Runs \<sigma> E'" by blast
  from Runs obtain E'' where E': "E' = lmap (\<lambda>(s, tl, s'). tl) E''"
    and Runs': "mthr.Runs_table \<sigma> E''" by(rule mthr.Runs_into_Runs_table)
  have "mthr.\<tau>Runs \<sigma> (tmap (\<lambda>(s, tl, s'). tl) id (tfilter None (\<lambda>(s, tl, s'). \<not> m\<tau>move s tl s') (tllist_of_llist (Some (llast (LCons \<sigma> (lmap (\<lambda>(s, tl, s'). s') E'')))) E'')))"
    (is "mthr.\<tau>Runs _ ?E'''")
    using Runs' by(rule mthr.Runs_table_into_\<tau>Runs)
  moreover
  have "(\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> []) = (\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> [] \<and> \<not> m\<tau>move s (t, ta) s')"
    by(rule ext)(auto dest: m\<tau>move_silentD)
  hence "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (llist_of_tllist ?E'''))"
    unfolding E E'
    by(subst (1 2) lconcat_lfilter_neq_LNil[symmetric])(simp add: lfilter_lmap lfilter_lfilter o_def split_def)
  ultimately show "E \<in> ?lhs" by(blast intro: \<E>.intros)
qed

end

lemma convert_RA_not_write:
  "ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
by(auto simp add: convert_RA_def)

lemma ta_seq_consist_convert_RA:
  "ta_seq_consist P vs (llist_of ((map NormalAction \<circ> convert_RA) ln))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume "Fin i < llength (llist_of ((map NormalAction \<circ> convert_RA) ln))"
    and "lnth (llist_of ((map NormalAction \<circ> convert_RA) ln)) i = NormalAction (ReadMem ad al v)"
  hence "ReadMem ad al v \<in> set (convert_RA ln)"
    by(auto simp add: in_set_conv_nth)
  hence False by(auto simp add: convert_RA_def)
  thus "\<exists>b. mrw_values P vs (list_of (ltake (Fin i) (llist_of ((map NormalAction \<circ> convert_RA) ln)))) (ad, al) = \<lfloor>(v, b)\<rfloor>" ..
qed

section {* Properties of external calls *}

context heap_base begin

lemma heap_clone_None_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' None"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using clone
by(cases)(auto dest: heap_ops_typeof_minimalD[OF minimal] del: equalityI)

lemma heap_copy_loc_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copy: "heap_copy_loc a a' al h ob h'"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using copy
by cases(auto dest: heap_ops_typeof_minimalD[OF minimal] del: equalityI)

lemma heap_copies_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copies: "heap_copies a a' als h obs h'"
  shows "dom (typeof_addr h') = dom (typeof_addr h)"
using copies
by induct(auto dest: heap_copy_loc_dom_typeof_addrD[OF minimal] del: equalityI)

lemma heap_clone_Some_dom_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows "dom (typeof_addr h') = insert a' (dom (typeof_addr h))"
using clone
by cases(auto del: equalityI dest!: heap_copies_dom_typeof_addrD[OF minimal] heap_ops_typeof_minimalD[OF minimal])

end

context heap begin

lemma heap_copy_loc_not_New: assumes "heap_copy_loc a a' al h ob h'"
  shows "NewHeapElem a'' x \<in> set ob \<Longrightarrow> False"
using assms
by(auto elim: heap_copy_loc.cases)

lemma heap_copies_not_New:
  assumes "heap_copies a a' als h obs h'" 
  and "NewHeapElem a'' x \<in> set obs"
  shows "False"
using assms
by induct(auto dest: heap_copy_loc_not_New)

lemma heap_clone_typeof_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows "typeof_addr h a' = None" 
  and "NewHeapElem a'' x \<in> set obs \<Longrightarrow> a'' = a' \<and> typeof_addr h' a' = Some (ty_of_htype x)"
using assms
by(fastsimp elim!: heap_clone.cases dest: new_obj_SomeD new_arr_SomeD hext_heap_copies heap_copies_not_New elim: hext_objD hext_arrD)+

lemma heap_clone_array_lengthD:
  "\<lbrakk> heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>; NewArr a'' T n \<in> set obs \<rbrakk>
  \<Longrightarrow> array_length h' a'' = n"
by(fastsimp elim!: heap_clone.cases dest: new_arr_SomeD hext_heap_copies heap_copies_not_New[where x="Array_type T n"] hext_arrD(2))

lemma red_external_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h a' = None \<and> typeof_addr h' a' = Some (ty_of_htype x)"
by(erule red_external.cases)(auto dest: heap_clone_typeof_addrD)

lemma red_external_aggr_New_typeof_addrD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_external_call P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> typeof_addr h a' = None \<and> typeof_addr h' a' = Some (ty_of_htype x)"
apply(auto simp add: is_external_call_def external_WT_defs.simps red_external_aggr_def split: split_if_asm)
apply(blast dest: heap_clone_typeof_addrD)+
done

lemma red_external_NewArr_lengthD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewArr a' T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length h' a' = n"
by(erule red_external.cases)(auto dest: heap_clone_array_lengthD)

lemma red_external_aggr_NewArr_lengthD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewArr a' T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_external_call P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> array_length h' a' = n"
by(auto simp add: is_external_call_def external_WT_defs.simps red_external_aggr_def split: split_if_asm dest: heap_clone_array_lengthD)

lemma heap_clone_New_same_addr_same:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! i = NewHeapElem a'' x" "i < length obs"
  and "obs ! j = NewHeapElem a'' x'" "j < length obs"
  shows "i = j"
using assms
apply cases
apply(fastsimp simp add: nth_Cons' gr0_conv_Suc in_set_conv_nth split: split_if_asm dest: heap_copies_not_New)+
done

lemma red_external_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; 
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto elim!: red_external.cases simp add: nth_Cons' split: split_if_asm dest: heap_clone_New_same_addr_same)

lemma red_external_aggr_New_same_addr_same:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_external_call P (the (typeof_addr h a)) M;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto simp add: is_external_call_def external_WT_defs.simps red_external_aggr_def nth_Cons' split: split_if_asm split_if_asm dest: heap_clone_New_same_addr_same)

lemma heap_clone_None_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' None"
  shows "typeof_addr h' = typeof_addr h"
using clone
by(cases)(auto dest: heap_ops_typeof_minimalD'[OF minimal])

lemma heap_copy_loc_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copy: "heap_copy_loc a a' al h ob h'"
  shows "typeof_addr h' = typeof_addr h"
using copy
by cases(auto dest: heap_ops_typeof_minimalD'[OF minimal])

lemma heap_copies_typeof_addrD:
  assumes minimal: "heap_ops_typeof_minimal"
  and copies: "heap_copies a a' als h obs h'"
  shows "typeof_addr h' = typeof_addr h"
using copies
by induct(auto dest: heap_copy_loc_typeof_addrD[OF minimal])

lemma heap_clone_new_heap_ops_obs:
  assumes minimal: "heap_ops_typeof_minimal"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  shows 
  "\<lbrakk> typeof_addr h' a'' = \<lfloor>T\<rfloor>; typeof_addr h a'' = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a'' CTn \<in> set obs \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a'' : CTn"
using clone
apply cases
 apply(drule heap_copies_typeof_addrD[OF minimal])
 apply(frule heap_ops_typeof_minimalD'[OF minimal])
 apply(drule new_obj_SomeD)
 apply(auto split: split_if_asm)[1]

apply(frule hext_heap_copies)
apply(drule heap_copies_typeof_addrD[OF minimal])
apply(frule heap_ops_typeof_minimalD'[OF minimal])
apply(drule new_arr_SomeD)
apply(clarsimp split: split_if_asm)
apply(rule exI)
apply(rule conjI)
 apply(rule disjI1)
 apply(rule refl)
apply simp
apply(drule hext_arrD(2)[where a=a'])
 apply simp
apply simp
done

lemma red_external_new_heap_ops_obs:
  assumes minimal: heap_ops_typeof_minimal
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows
  "\<lbrakk> typeof_addr h' a' = Some T; typeof_addr h a' = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a' : CTn"
using red
apply cases
apply (auto dest: heap_ops_typeof_minimalD[OF minimal] heap_clone_None_typeof_addrD[OF minimal] heap_clone_new_heap_ops_obs[OF minimal])
done

lemma red_external_aggr_new_heap_ops_obs:
  assumes minimal: heap_ops_typeof_minimal
  and red: "(ta, va, h') \<in> red_external_aggr P t a M vs h"
  and iec: "is_external_call P (the (typeof_addr h a)) M"
  shows
  "\<lbrakk> typeof_addr h' a' = Some T; typeof_addr h a' = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> h' \<turnstile>a a' : CTn"
using red iec
apply(auto simp add: is_external_call_def external_WT_defs.simps red_external_aggr_def split: split_if_asm)
apply(auto dest: heap_ops_typeof_minimalD[OF minimal] heap_clone_new_heap_ops_obs[OF minimal] heap_clone_None_typeof_addrD[OF minimal])
done

lemma heap_copy_loc_read_addrD:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ReadMem ad al' v \<in> set ob"
  shows "ad = a"
using assms by cases auto

lemma heap_copies_read_addrD:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms by induct (auto dest: heap_copy_loc_read_addrD)

lemma heap_clone_read_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms by cases(auto dest: heap_copies_read_addrD)

lemma red_external_read_addrD:
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> {t, a} \<union> {a. Addr a \<in> set vs} \<union> set start_addrs"
using assms by cases(auto dest: heap_clone_read_addrD)


lemma heap_copy_loc_read_typeable:
  assumes "heap_copy_loc a a' al h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "P,h \<turnstile> a@al : T"
  shows "ad = a \<and> al'= al"
using assms by cases auto

lemma heap_copies_read_typeable:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  shows "ad = a \<and> al' \<in> set als"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts`
  obtain T Ts' where Ts [simp]: "Ts = T # Ts'"
    and "P,h \<turnstile> a@al : T" 
    and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `ReadMem ad al' v \<in> set (ob @ obs)`
  show ?case unfolding set_append Un_iff
  proof
    assume "ReadMem ad al' v \<in> set ob"
    with `heap_copy_loc a a' al h ob h'`
    have "ad = a \<and> al'= al" using `P,h \<turnstile> a@al : T`
      by(rule heap_copy_loc_read_typeable)
    thus ?thesis by simp
  next
    assume "ReadMem ad al' v \<in> set obs"
    moreover from `heap_copy_loc a a' al h ob h'`
    have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    from `list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'`
    have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
      by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h'`])
    ultimately have "ad = a \<and> al' \<in> set als" by(rule Cons)
    thus ?thesis by simp
  qed
qed

lemma heap_clone_read_typeable:
  assumes clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and read: "ReadMem ad al v \<in> set obs"
  shows "ad = a \<and> (\<exists>T'. P,h \<turnstile> ad@al : T')"
using clone
proof cases
  case (ObjClone C H' FDTs obs')
  let ?als = "map (\<lambda>((F, D), Tm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  note `heap_copies a a' ?als H' obs' h'`
  moreover
  from `obs = NewObj a' C # obs'` read 
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover
  from `new_obj h C = (H', \<lfloor>a'\<rfloor>)` have "h \<unlhd> H'" by(rule hext_new_obj)
  hence "typeof_addr H' a = \<lfloor>Class C\<rfloor>" using `typeof_addr h a = \<lfloor>Class C\<rfloor>`
    by(rule typeof_addr_hext_mono)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts"
    using `P \<turnstile> C has_fields FDTs`
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain F D T where [simp]: "al = CField D F" and "((F, D), T) \<in> set FDTs" by auto
  with type `h \<unlhd> H'` `typeof_addr h a = \<lfloor>Class C\<rfloor>` show ?thesis 
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp elim!: ballE[where x="((F, D), T)"] addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
next
  case (ArrClone T n H' obs')
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  note `heap_copies a a' ?als H' obs' h'`
  moreover from `obs = NewArr a' T n # obs'` read
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover from `new_arr h T n = (H', \<lfloor>a'\<rfloor>)`
  have "h \<unlhd> H'" by(rule hext_new_arr)
  with `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `n = array_length h a`
  have "typeof_addr H' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>" "array_length H' a = n"
    by(auto dest: typeof_addr_hext_mono hext_arrD)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain n' where [simp]: "al = ACell n'" and "n' < n" by auto
  with type `h \<unlhd> H'` `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `n = array_length h a`
  show ?thesis
    by(fastsimp dest: list_all2_nthD[where p=n'] elim: addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
qed

lemma red_external_read_mem_typeable:
  assumes wf: "wf_prog wfmd P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using red read
by cases(auto dest: heap_clone_read_typeable intro: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf])

end

context heap_conf_read begin

lemma heap_copy_loc_write_typeable:
  assumes "heap_copy_loc ad ad' al h obs h'"
  and "WriteMem ad'' al'' v \<in> set obs"
  and "hconf h"
  and "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
  shows "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
using assms
by cases(auto dest!: heap_read_conf hext_heap_write intro: addr_loc_type_hext_mono conf_hext)

lemma heap_copies_write_typeable:
  assumes "heap_copies ad ad' als h obs h'"
  and "WriteMem ad'' al'' v \<in> set obs"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts" 
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts"
  shows "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  note copy = `heap_copy_loc ad ad' al h ob h'`
  from `list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) (al # als) Ts`
  obtain T Ts' where Ts: "Ts = T # Ts'"
    and alT: "P,h \<turnstile> ad@al : T" 
    and als: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from `list_all2 (addr_loc_type P h ad') (al # als) Ts` Ts
  have alT': "P,h \<turnstile> ad'@al : T"
    and als': "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts'" by simp_all

  from `WriteMem ad'' al'' v \<in> set (ob @ obs)`
  have "WriteMem ad'' al'' v \<in> set ob \<or> WriteMem ad'' al'' v \<in> set obs" by simp
  thus ?case
  proof
    assume "WriteMem ad'' al'' v \<in> set ob"
    with copy have "\<exists>T'. P,h' \<turnstile> ad''@al'' : T' \<and> P,h' \<turnstile> v :\<le> T'"
      using `hconf h` alT alT' by(rule heap_copy_loc_write_typeable)
    moreover from `heap_copies ad ad' als h' obs h''`
    have "h' \<unlhd> h''" by(rule hext_heap_copies)
    ultimately show ?thesis by(auto intro: conf_hext addr_loc_type_hext_mono)
  next
    assume "WriteMem ad'' al'' v \<in> set obs"
    moreover from copy `hconf h` alT alT'
    have "hconf h'" by(rule hconf_heap_copy_loc_mono)
    moreover from copy have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    with als have "list_all2 (\<lambda>al T. P,h' \<turnstile> ad@al : T) als Ts'"
      by -(erule list_all2_mono[OF _ addr_loc_type_hext_mono])
    moreover from als' `h \<unlhd> h'` have "list_all2 (\<lambda>al T. P,h' \<turnstile> ad'@al : T) als Ts'"
      by -(erule list_all2_mono[OF _ addr_loc_type_hext_mono])
    ultimately show ?thesis by(rule Cons.hyps)
  qed
qed

lemma heap_clone_write_typeable:
  assumes wf: "wf_prog wfmd P"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "write": "WriteMem ad al v \<in> set obs"
  and hconf: "hconf h"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')
  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (fst \<circ> snd) FDTs"
  note `heap_copies a a' ?als h'' obs' h'` 
  moreover from "write" `obs = NewObj a' C # obs'`
  have "WriteMem ad al v \<in> set obs'" by simp
  moreover from `typeof_addr h a = \<lfloor>Class C\<rfloor>` `hconf h` have "is_class P C"
    by(auto dest: typeof_addr_is_type)
  from `new_obj h C = (h'', \<lfloor>a'\<rfloor>)` have "h \<unlhd> h''" "hconf h''"
    by(rule hext_heap_ops hconf_new_obj_mono[OF _ `hconf h` `is_class P C`])+
  note `hconf h''` 
  moreover from wf FDTs have "distinct (map fst FDTs)"
    by(rule has_fields_distinct)
  with `typeof_addr h a = \<lfloor>Class C\<rfloor>` FDTs
  have "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(rule list_all2_mono)(rule addr_loc_type_hext_mono[OF _ `h \<unlhd> h''`])
  moreover from `new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have "typeof_addr h'' a' = \<lfloor>Class C\<rfloor>" by(auto dest: new_obj_SomeD)
  with FDTs `distinct (map fst FDTs)`
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  ultimately show ?thesis by(rule heap_copies_write_typeable)
next
  case (ArrClone T n h'' obs')
  note [simp] = `n = array_length h a`
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  note `heap_copies a a' (map ACell [0..<n]) h'' obs' h'`
  moreover from "write" `obs = NewArr a' T n # obs'`
  have "WriteMem ad al v \<in> set obs'" by simp
  moreover from `typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `hconf h` have "is_type P T"
    by(auto dest: typeof_addr_is_type)
  from `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` have "h \<unlhd> h''" "hconf h''"
    by(rule hext_heap_ops hconf_new_arr_mono[OF _ `hconf h` `is_type P T`])+
  note `hconf h''`
  moreover from `h \<unlhd> h''` `typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have type'a: "typeof_addr h'' a = \<lfloor>Array T\<rfloor>"
    and [simp]: "array_length h'' a = array_length h a" by(auto intro: hext_arrD)
  from type'a have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  moreover from `new_arr h T n = (h'', \<lfloor>a'\<rfloor>)`
  have "typeof_addr h'' a' = \<lfloor>Array T\<rfloor>" "array_length h'' a' = array_length h a"
    by(auto dest: new_arr_SomeD)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI addr_loc_type.intros)
  ultimately show ?thesis by(rule heap_copies_write_typeable)
qed

lemma red_external_write_typeable:
  assumes wf_prog: "wf_prog wfmd P"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and "write": "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and hconf: "hconf h"
  shows "\<exists>T'. P,h' \<turnstile> ad@al : T' \<and> P,h' \<turnstile> v :\<le> T'"
using red "write" hconf
apply cases
apply(fastsimp elim: typeof_addr_hext_mono[OF hext_heap_write] intro: addr_loc_type.intros wf_sub_Thread_has_interrupted_flag[OF wf_prog] heap_clone_write_typeable[OF wf_prog])+
done

end

context heap begin

lemma mrw_values_start_heap_obs_typeable:
  assumes "mrw_values P empty (map NormalAction start_heap_obs) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,start_heap \<turnstile> ad@al : T \<and> P,start_heap \<turnstile> v :\<le> T"
proof -
  from mrw_values_eq_SomeD[OF assms]
  obtain obs' wa obs'' 
    where eq: "map NormalAction start_heap_obs = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  from `is_write_action wa` show ?thesis
  proof cases
    case (WriteMem ad' al' v')
    with vwa adal eq have "WriteMem ad al v \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    thus ?thesis by(rule start_heap_write_typeable)
  next
    case (NewObj ad' C)
    with vwa adal eq have "NewObj ad C \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    hence "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>" by(rule NewObj_start_heap_obsD)
    thus ?thesis using adal vwa NewObj
      by(fastsimp simp add: has_field_def intro: addr_loc_type.intros)
  next
    case (NewArr ad' T n)
    with vwa adal eq have "NewArr ad T n \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv)
    hence "typeof_addr start_heap ad = \<lfloor>Array T\<rfloor>"
      and "array_length start_heap ad = n" by(rule NewArr_start_heap_obsD)+
    thus ?thesis using adal vwa NewArr by(auto intro: addr_loc_type.intros)
  qed
qed

end

section {* Cut and update for external calls *}

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

lemma heap_copy_loc_cut_and_update:
  assumes vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and type: "P,h \<turnstile>jmm' a@al : T" "P,h \<turnstile>jmm' a'@al : T"
  shows "\<exists>obs'' h''. jmm'_heap_copy_loc P a a' al h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction obs'') vs"
proof -
  from type(1) have "(a, al) \<in> dom vs" using dom_vs by blast
  then obtain v' b where v'b: "vs (a, al) = \<lfloor>(v', b)\<rfloor>" by auto
  from vs[OF this] type have conf: "P,h \<turnstile>jmm' v' :\<le> T" by(auto dest: jmm'.addr_loc_type_fun)
  let ?obs'' = "[ReadMem a al v', WriteMem a' al v']"
  from type(1) conf have "jmm_heap_read' P h a al v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  moreover from jmm'.heap_write_total[OF type(2) conf] 
  obtain h'' where "jmm_heap_write' P h a' al v' h''" ..
  ultimately have "jmm'_heap_copy_loc P a a' al h ?obs'' h''" ..
  moreover have "ta_seq_consist P vs (llist_of (map NormalAction ?obs''))"
    using v'b by simp
  moreover have "eq_upto_seq_inconsist P (map NormalAction [ReadMem a al v, WriteMem a' al v]) (map NormalAction ?obs'') vs"
    using v'b by(simp)
  ultimately show ?thesis by blast
qed

lemma eq_upto_seq_inconsist_appendI:
  "\<lbrakk> eq_upto_seq_inconsist P obs OBS vs;
     \<lbrakk> ta_seq_consist P vs (llist_of obs) \<rbrakk> \<Longrightarrow> eq_upto_seq_inconsist P obs' OBS' (mrw_values P vs OBS) \<rbrakk>
  \<Longrightarrow> eq_upto_seq_inconsist P (obs @ obs') (OBS @ OBS') vs"
apply(induct obs arbitrary: vs OBS)
 apply simp
apply(auto simp add: eq_upto_seq_inconsist_Cons1)
apply(simp split: action.split obs_event.split)
apply auto
done

lemma heap_copies_cut_and_update:
  assumes copies: "jmm'_heap_copies P a a' als h obs h'"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
    (is "PROP ?vs vs h")
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and type1: "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) als Ts"
  and type2: "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) als Ts"
  and hconf: "P \<turnstile>jmm' h \<surd>"
  shows "\<exists>obs'' h''. jmm'_heap_copies P a a' als h obs'' h'' \<and>
                     ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
    (is "?concl als h obs vs")
using assms
proof(induct arbitrary: h Ts vs)
  case Nil thus ?case by(auto intro: jmm'.heap_copies.Nil)
next
  case (Cons al H ob h' als obs h'' h Ts vs)
  note vs = `PROP ?vs vs h`
    and dom_vs = `{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs`
  note type1 = `list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) (al # als) Ts`
    and type2 = `list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) (al # als) Ts`
  note hconf = `P \<turnstile>jmm' h \<surd>`

  from type1 obtain T Ts' where Ts: "Ts = T # Ts'"
    and type1': "P,h \<turnstile>jmm' a@al : T"
    and type1'': "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from type2 Ts have type2': "P,h \<turnstile>jmm' a'@al : T"
    and type2'': "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a'@al : T) als Ts'"
    by simp_all
  from `jmm'_heap_copy_loc P a a' al H ob h'`
  obtain v where "ob = [ReadMem a al v, WriteMem a' al v]" by cases
  with heap_copy_loc_cut_and_update[OF vs dom_vs type1' type2', where ?b1="\<lambda>_ _ _ b. b" and v=v]
  obtain OB H' where hcl: "jmm'_heap_copy_loc P a a' al h OB H'"
    and sc: "ta_seq_consist P vs (llist_of (map NormalAction OB))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction ob) (map NormalAction OB) vs" by auto
  from hcl have hext: "h \<unlhd>jmm' H'" by(rule jmm'.hext_heap_copy_loc)

  let ?vs' = "mrw_values P vs (map NormalAction OB)"
  have "PROP ?vs ?vs' H'"
  proof -
    fix ad al v b
    assume vs': "?vs' (ad, al) = \<lfloor>(v, b)\<rfloor>"
    show "\<exists>T. P,H' \<turnstile>jmm' ad@al : T \<and> P,H' \<turnstile>jmm' v :\<le> T"
    proof(cases "vs (ad, al) = \<lfloor>(v, b)\<rfloor>")
      case True 
      from hext vs[OF True] show ?thesis
        by(auto intro: jmm'.addr_loc_type_hext_mono jmm'.conf_hext)
    next
      case False
      with mrw_values_eq_SomeD[OF vs']
      obtain obs' wa obs'' 
        where eq: "map NormalAction OB = obs' @ wa # obs''"
        and "is_write_action wa"
        and adal: "(ad, al) \<in> action_loc_aux P wa"
        and vwa: "value_written_aux P wa al = v"
        by blast
      with hcl have "\<not> is_new_action wa"
        by(auto simp add: map_eq_append_conv elim!: is_new_action.cases dest: jmm'.heap_copy_loc_not_New)
      with `is_write_action wa` adal vwa have "wa = NormalAction (WriteMem ad al v)"
        by cases auto
      with eq have "WriteMem ad al v \<in> set OB" by(auto simp add: map_eq_append_conv)
      with hcl show ?thesis using hconf type1' type2' by(rule jmm'.heap_copy_loc_write_typeable)
    qed
  qed
  moreover
  from jmm'.heap_copy_loc_typeof_addrD[OF jmm'_heap_ops_typeof_minimal hcl]
    mrw_values_dom_mono[where vs=vs and P=P and obs="map NormalAction OB"] dom_vs jmm'.hext_arrD(2)[OF hext]
  have "{(ad, al). \<exists>T. P,H' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs'"
    by(fastsimp elim: jmm'.addr_loc_type.cases subsetD intro: jmm'.addr_loc_type.intros iff del: domIff)
  moreover from type1'' have "list_all2 (\<lambda>al T. P,H' \<turnstile>jmm' a@al : T) als Ts'"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from type2'' have "list_all2 (\<lambda>al T. P,H' \<turnstile>jmm' a'@al : T) als Ts'"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from hcl hconf type1' type2'
  have "P \<turnstile>jmm' H' \<surd>" by(rule jmm'.hconf_heap_copy_loc_mono)
  ultimately have "?concl als H' obs ?vs'" by(rule Cons.hyps)
  then obtain OBS H''
    where copies: "jmm'_heap_copies P a a' als H' OBS H''"
    and sc': "ta_seq_consist P ?vs' (llist_of (map NormalAction OBS))"
    and eq': "eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction OBS) ?vs'" by blast
  from hcl copies have "jmm'_heap_copies P a a' (al#als) h (OB @ OBS) H''" ..
  moreover from sc sc' have "ta_seq_consist P vs (llist_of (map NormalAction (OB @ OBS)))"
    by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
  moreover from eq eq' sc
  have "eq_upto_seq_inconsist P (map NormalAction (ob @ obs)) (map NormalAction (OB @ OBS)) vs"
    by(simp add: eq_upto_seq_inconsist_appendI)
  ultimately show ?case by blast
qed

lemma heap_clone_cut_and_update:
  assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile>jmm' ad@al : T \<and> P,h \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,h \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and clone: "jmm'_heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and hconf: "P \<turnstile>jmm' h \<surd>"
  shows "\<exists>obs'' h''. jmm'_heap_clone P h a h'' \<lfloor>(obs'', a')\<rfloor> \<and>
          ta_seq_consist P vs (llist_of (map NormalAction obs'')) \<and>
          eq_upto_seq_inconsist P (map NormalAction obs) (map NormalAction obs'') vs"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')
  
  note FDTs = `P \<turnstile> C has_fields FDTs`
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (fst \<circ> snd) FDTs"
  let ?vs = "mrw_value P vs (NormalAction (NewObj a' C))"

  from `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "jmm_typeof_addr h'' a' = \<lfloor>Class C\<rfloor>"
    and hext: "h \<unlhd>jmm' h''"
    and dom_typeof: "dom (jmm_typeof_addr h'') = insert a' (dom (jmm_typeof_addr h))"
    and type_a'': "jmm_typeof_addr h a' = None"
    by(auto dest: jmm'.new_obj_SomeD jmm'.hext_new_obj jmm'.heap_ops_typeof_minimalD[OF jmm'_heap_ops_typeof_minimal] del: subsetI)

  note `jmm'_heap_copies P a a' ?als h'' obs' h'`
  moreover {
    fix ad al v b
    assume "?vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
    hence "\<exists>T. P,h'' \<turnstile>jmm' ad@al : T \<and> P,h'' \<turnstile>jmm' v :\<le> T"
      using FDTs type_a' hext
      apply(auto split: split_if_asm)
      prefer 4
      apply(fastsimp simp add: has_field_def dest: has_fields_fun vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext)
      apply(fastsimp simp add: has_field_def dest: has_fields_fun vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext notE)+
      done }
  moreover { fix ad al T
    assume adal: "P,h'' \<turnstile>jmm' ad@al : T"
    have "(ad, al) \<in> dom ?vs"
    proof(cases "\<exists>T. P,h \<turnstile>jmm' ad@al : T")
      case True
      with dom_vs[THEN subsetD, of "(ad, al)"]
      have "(ad, al) \<in> dom vs" by auto
      also note mrw_value_dom_mono
      finally show ?thesis .
    next
      case False
      have "ad = a'" using False adal dom_typeof[THEN equalityD1, THEN subsetD, of ad] hext
        by(fastsimp elim: jmm'.addr_loc_type.cases dest: jmm'.typeof_addr_hext_mono jmm'.hext_arrD(2)[OF hext] intro: jmm'.addr_loc_type.intros)+
      with adal type_a' show ?thesis by cases fastsimp+
    qed }
  hence "{(ad, al). \<exists>T. P,h'' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs" by blast
  moreover from wf FDTs have "distinct (map fst FDTs)"
    by(rule has_fields_distinct)
  with `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` FDTs
  have "list_all2 (\<lambda>al T. P,h \<turnstile>jmm' a@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: jmm'.addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a@al : T) ?als ?Ts"
    by(rule list_all2_mono)(rule jmm'.addr_loc_type_hext_mono[OF _ hext])
  moreover from FDTs `distinct (map fst FDTs)` type_a'
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastsimp intro!: jmm'.addr_loc_type.intros map_of_SomeI simp add: has_field_def distinct_fst_def)
  moreover from `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` hconf have "is_class P C"
    by(auto dest: jmm'.typeof_addr_is_type)
  with `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)` hconf have "P \<turnstile>jmm' h'' \<surd>"
    by(rule jmm'.hconf_new_obj_mono)
  ultimately
  have "\<exists>obs'' h'''. jmm'_heap_copies P a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update)
  then obtain obs'' h''' where copies: "jmm'_heap_copies P a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `jmm_typeof_addr h a = \<lfloor>Class C\<rfloor>` `jmm_new_obj h C = (h'', \<lfloor>a'\<rfloor>)` FDTs copies
  have "jmm'_heap_clone P h a h''' \<lfloor>(NewObj a' C # obs'', a')\<rfloor>"
    by(rule jmm'.heap_clone.ObjClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewObj a' C # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewObj a' C # obs')) (map NormalAction (NewObj a' C # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewObj a' C # obs'` by blast
next
  case (ArrClone T n h'' obs')

  note [simp] = `n = jmm_array_length h a`
  let ?als = "map ACell [0..<n]"
  let ?Ts = "replicate n T"
  let ?vs = "mrw_value P vs (NormalAction (NewArr a' T n))"

  from `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)`
  have type_a': "jmm_typeof_addr h'' a' = \<lfloor>Array T\<rfloor>"
    and hext: "h \<unlhd>jmm' h''"
    and dom_typeof: "dom (jmm_typeof_addr h'') = insert a' (dom (jmm_typeof_addr h))"
    and type_a'': "jmm_typeof_addr h a' = None"
    and len: "jmm_array_length h'' a' = n"
    by(auto dest: jmm'.new_arr_SomeD jmm'.hext_new_arr jmm'.heap_ops_typeof_minimalD[OF jmm'_heap_ops_typeof_minimal] del: subsetI)

  note `jmm'_heap_copies P a a' ?als h'' obs' h'`
  moreover {
    fix ad al v b
    assume "?vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
    hence "\<exists>T. P,h'' \<turnstile>jmm' ad@al : T \<and> P,h'' \<turnstile>jmm' v :\<le> T"
      using type_a' hext len
      by(fastsimp dest: vs intro: jmm'.addr_loc_type.intros elim: jmm'.addr_loc_type_hext_mono jmm'.conf_hext elim: notE split: split_if_asm) }
  moreover { fix ad al T
    assume adal: "P,h'' \<turnstile>jmm' ad@al : T"
    have "(ad, al) \<in> dom ?vs"
    proof(cases "\<exists>T. P,h \<turnstile>jmm' ad@al : T")
      case True
      with dom_vs[THEN subsetD, of "(ad, al)"]
      have "(ad, al) \<in> dom vs" by auto
      also note mrw_value_dom_mono
      finally show ?thesis .
    next
      case False
      have "ad = a'" using False adal dom_typeof[THEN equalityD1, THEN subsetD, of ad] hext len
        by(fastsimp elim: jmm'.addr_loc_type.cases dest: jmm'.typeof_addr_hext_mono jmm'.hext_arrD(2)[OF hext] intro: jmm'.addr_loc_type.intros)+
      with adal type_a' len show ?thesis by cases fastsimp+
    qed }
  hence "{(ad, al). \<exists>T. P,h'' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs" by blast
  moreover from hext `jmm_typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have type'a: "jmm_typeof_addr h'' a = \<lfloor>Array T\<rfloor>"
    and [simp]: "jmm_array_length h'' a = jmm_array_length h a"
    by(auto intro: jmm'.hext_arrD)
  from type'a have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI jmm'.addr_loc_type.intros)
  moreover from type_a' len have "list_all2 (\<lambda>al T. P,h'' \<turnstile>jmm' a'@al : T) ?als ?Ts"
    by(fastsimp intro: list_all2_all_nthI jmm'.addr_loc_type.intros)
  moreover from `jmm_typeof_addr h a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` hconf have "is_type P T"
    by(auto dest: jmm'.typeof_addr_is_type)
  with `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` hconf have "P \<turnstile>jmm' h'' \<surd>"
    by(rule jmm'.hconf_new_arr_mono)
  ultimately 
  have "\<exists>obs'' h'''. jmm'_heap_copies P a a' ?als h'' obs'' h''' \<and>
                     ta_seq_consist P ?vs (llist_of (map NormalAction obs'')) \<and>
                     eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by(rule heap_copies_cut_and_update)
  then obtain obs'' h''' where copies: "jmm'_heap_copies P a a' ?als h'' obs'' h'''"
    and sc: "ta_seq_consist P ?vs (llist_of (map NormalAction obs''))"
    and eq: "eq_upto_seq_inconsist P (map NormalAction obs') (map NormalAction obs'') ?vs"
    by blast
  from `jmm_typeof_addr h a = \<lfloor>Array T\<rfloor>` `n = jmm_array_length h a` `jmm_new_arr h T n = (h'', \<lfloor>a'\<rfloor>)` copies
  have "jmm'_heap_clone P h a h''' \<lfloor>(NewArr a' T n # obs'', a')\<rfloor>"
    by(rule jmm'.heap_clone.ArrClone)
  moreover from sc have "ta_seq_consist P vs (llist_of (map NormalAction (NewArr a' T n # obs'')))" by simp
  moreover from eq have "eq_upto_seq_inconsist P (map NormalAction (NewArr a' T n # obs')) (map NormalAction (NewArr a' T n # obs'')) vs" by simp
  ultimately show ?thesis unfolding `obs = NewArr a' T n # obs'` by blast
qed

context final_thread begin

lemma red_external_cut_and_update:
  assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and red: "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs'),shr s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>"
  and aok: "actions_ok s t ta"
  and hconf: "P \<turnstile>jmm' (shr s) \<surd>"
  shows "\<exists>ta'' va'' h''. P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta''\<rightarrow>ext \<langle>va'', h''\<rangle> \<and> 
                         actions_ok s t ta'' \<and>
                         ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)) \<and>
                         eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) vs"
using red aok
proof(cases)
  case (RedWaitInterrupt C)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b' where v: "v = Bool b'" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWaitInterrupt aok 
    by(cases b')(fastsimp intro: jmm'.RedWaitInterrupt jmm'.RedWait simp add: lock_ok_las_def finfun_upd_apply wset_actions_ok_def split: split_if_asm)+
next
  case (RedWait C)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b' where v: "v = Bool b'" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWait aok jmm'.heap_write_total[OF adal, of "Bool False"]
    by(cases b')(fastsimp intro: jmm'.RedWaitInterrupt jmm'.RedWait simp add: lock_ok_las_def finfun_upd_apply wset_actions_ok_def split: split_if_asm)+
next
  case (RedWaitInterrupted C b')
  from wf `P \<turnstile> C \<preceq>\<^sup>* Thread`
  have "P \<turnstile> C has interrupted_flag:Boolean (\<lparr>volatile = True\<rparr>) in Thread"
    by(rule wf_sub_Thread_has_interrupted_flag)
  with `jmm_typeof_addr (shr s) t = \<lfloor>Class C\<rfloor>`
  have adal: "P,shr s \<turnstile>jmm' t@interrupted_flag_loc : Boolean" ..
  hence "(t, interrupted_flag_loc) \<in> dom vs" using dom_vs by blast
  then obtain v b where vb: "vs (t, interrupted_flag_loc) = \<lfloor>(v, b)\<rfloor>" by auto
  from vs[OF this] adal have "P,shr s \<turnstile>jmm' v :\<le> Boolean" by(auto dest: jmm'.addr_loc_type_fun)
  then obtain b'' where v: "v = Bool b''" by(auto simp add: jmm'.conf_def)
  from adal have "jmm_heap_read' P (shr s) t interrupted_flag_loc (Bool b'')"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  thus ?thesis using vb v RedWaitInterrupted aok by(fastsimp intro: jmm'.RedWaitInterrupted)
next
  case (RedClone obs a')
  with heap_clone_cut_and_update[OF wf vs dom_vs `jmm'_heap_clone P (shr s) a h' \<lfloor>(obs, a')\<rfloor>` hconf, of "\<lambda>_ _ _ b. b"]
  show ?thesis using aok
    by(fastsimp intro: jmm'.red_external.RedClone)
qed(fastsimp intro: jmm'.red_external.intros)+

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

section {* Sequentially consistent completion from cut and update *}

definition Status_no_wait_locks :: "('l,'t,status \<times> 'x) thread_info \<Rightarrow> bool"
where
  "Status_no_wait_locks ts \<longleftrightarrow> 
  (\<forall>t status x ln. ts t = \<lfloor>((status, x), ln)\<rfloor> \<longrightarrow> status \<noteq> Running \<longrightarrow> ln = no_wait_locks)"

lemma Status_no_wait_locks_PreStartD:
  "\<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((PreStart, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locks_FinishedD:
  "\<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((Finished, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locksI:
  "(\<And>t status x ln. \<lbrakk> ts t = \<lfloor>((status, x), ln)\<rfloor>; status = PreStart \<or> status = Finished \<rbrakk> \<Longrightarrow> ln = no_wait_locks)
  \<Longrightarrow> Status_no_wait_locks ts"
unfolding Status_no_wait_locks_def 
apply clarify
apply(case_tac status)
apply auto
done

context heap_base begin

lemma Status_no_wait_locks_start_state:
  "Status_no_wait_locks (thr (init_fin_lift_state status (start_state f P C M vs)))"
by(clarsimp simp add: Status_no_wait_locks_def init_fin_lift_state_def start_state_def split_beta)

end

context multithreaded_base begin

lemma init_fin_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  shows "Status_no_wait_locks (thr s')"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with ok show ?thesis
    by(auto intro!: Status_no_wait_locksI dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD split: split_if_asm)
next
  case redT_normal
  show ?thesis
  proof(rule Status_no_wait_locksI)
    fix t' status' x' ln'
    assume tst': "thr s' t' = \<lfloor>((status', x'), ln')\<rfloor>"
      and status: "status' = PreStart \<or> status' = Finished"
    show "ln' = no_wait_locks"
    proof(cases "thr s t'")
      case None
      with redT_normal tst' show ?thesis
        by(fastsimp elim!: init_fin.cases dest: redT_updTs_new_thread simp add: final_thread.actions_ok_iff split: split_if_asm)
    next
      case (Some sxln)
      obtain status'' x'' ln'' 
        where [simp]: "sxln = ((status'', x''), ln'')" by(cases sxln) auto
      show ?thesis
      proof(cases "fst tta = t'")
        case True
        with redT_normal tst' status show ?thesis by(auto simp add: expand_finfun_eq fun_eq_iff)
      next
        case False
        with tst' redT_normal Some status have "status'' = status'" "ln'' = ln'" 
          by(force dest: redT_updTs_Some simp add: final_thread.actions_ok_iff)+
        with ok Some status show ?thesis
          by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      qed
    qed
  qed
qed

lemma init_fin_Running_InitialThreadAction:
  assumes redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "tta = (t, \<epsilon>\<lbrace>\<^bsub>o\<^esub>InitialThreadAction\<rbrace>)"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with running not_running show ?thesis by(auto split: split_if_asm)
next
  case redT_normal
  show ?thesis
  proof(cases "thr s t")
    case None
    with redT_normal running not_running show ?thesis
      by(fastsimp simp add: final_thread.actions_ok_iff elim: init_fin.cases dest: redT_updTs_new_thread split: split_if_asm)
  next
    case (Some a)
    with redT_normal running not_running show ?thesis
      apply(cases a)
      apply(auto simp add: final_thread.actions_ok_iff split: split_if_asm elim: init_fin.cases)
      apply((drule (1) redT_updTs_Some)?, fastsimp)+
      done
  qed
qed

end

context if_\<tau>multithreaded begin

lemma init_fin_\<tau>rtrancl3p_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "if.mthr.\<tau>rtrancl3p s ttas s'"
  shows "Status_no_wait_locks (thr s')"
using redT ok
by(induct)(auto dest: init_fin_preserve_Status_no_wait_locks)

lemma init_fin_silent_move_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "if.mthr.silent_move s s'"
  shows "Status_no_wait_locks (thr s')"
using redT ok
by(cases)(rule init_fin_preserve_Status_no_wait_locks)

lemma init_fin_silent_moves_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "if.mthr.silent_moves s s'"
  shows "Status_no_wait_locks (thr s')"
using redT ok
by(induct)(auto dest: init_fin_silent_move_preserve_Status_no_wait_locks)

lemma init_fin_silent_move_Running_invariant:
  assumes "if.mthr.silent_move s s'"
  shows "(\<exists>x ln. thr s t = \<lfloor>((Running, x), ln)\<rfloor>) \<longleftrightarrow> (\<exists>x ln. thr s' t = \<lfloor>((Running, x), ln)\<rfloor>)"
using assms
apply cases
apply(auto elim!: if.m\<tau>move.cases init_fin_\<tau>move.cases if.redT.cases split: split_if_asm simp del: thread_oks_convert_new_thread_action)
 apply(fastsimp elim: redT_updTs_Some[where t=t])
apply(case_tac "au t")
 apply(fastsimp dest: redT_updTs_new_thread simp add: convert_extTA_def)[1]
apply(auto simp del: thread_oks_convert_new_thread_action dest: redT_updTs_Some)
done

lemma init_fin_silent_moves_Running_invariant:
  assumes "if.mthr.silent_moves s s'"
  shows "(\<exists>x ln. thr s t = \<lfloor>((Running, x), ln)\<rfloor>) \<longleftrightarrow> (\<exists>x ln. thr s' t = \<lfloor>((Running, x), ln)\<rfloor>)"
using assms
by(induct)(simp_all add: init_fin_silent_move_Running_invariant)

lemma init_fin_\<tau>rtrancl3p_Running_InitialThreadAction:
  assumes redT: "if.mthr.\<tau>rtrancl3p s ttas s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "(t, \<epsilon>\<lbrace>\<^bsub>o\<^esub>InitialThreadAction\<rbrace>) \<in> set ttas"
using redT not_running running
proof(induct)
  case \<tau>rtrancl3p_refl thus ?case by(fastsimp)
next
  case \<tau>rtrancl3p_step thus ?case
    by(cases "\<exists>x ln. thr s' t = \<lfloor>((Running, x), ln)\<rfloor>")(fastsimp dest: init_fin_Running_InitialThreadAction)+
next
  case (\<tau>rtrancl3p_\<tau>step s s' tls s'' tl)
  from `if.redT s tl s'` `if.m\<tau>move s tl s'`
  have "if.mthr.silent_move s s'" ..
  from init_fin_silent_move_Running_invariant[OF this, of t] `\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>`
  have "\<And>x ln. thr s' t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>" by auto
  with \<tau>rtrancl3p_\<tau>step.hyps `thr s'' t = \<lfloor>((Running, x'), ln')\<rfloor>` show ?case by blast
qed

end


locale Jinja_executions_aux =
  if_\<tau>multithreaded final r "convert_RA" \<tau>move +
  jmm!: executions_sc "lappend (llist_of (lift_start_obs start_tid start_heap_obs')) ` if.\<E> start_state" P
  for final :: "'x \<Rightarrow> bool"
  and r :: "(addr, thread_id, 'x, 'm, 'w, obs_event) semantics"
  and \<tau>move :: "(addr, thread_id, 'x, 'm, 'w, obs_event) \<tau>moves" 
  and start_heap_obs' :: "obs_event list"
  and start_tid :: "thread_id"
  and start_state :: "(addr, thread_id, status \<times> 'x, 'm, 'w) state"
  and P :: "'md prog" +
  assumes start_heap_obs'_not_Read: "\<And>ad al v. ReadMem ad al v \<notin> set start_heap_obs'"
  and thr_start_state_RunningD: "thr start_state t = \<lfloor>((Running, x), ln)\<rfloor> \<Longrightarrow> t = start_tid"
  and start_state_Status_no_wait_locks: "Status_no_wait_locks (thr start_state)"

sublocale Jinja_executions_aux < jmm_\<tau>multithreaded 
  init_fin_final
  init_fin
  "map NormalAction \<circ> convert_RA"
  init_fin_\<tau>move 
  P
.

context Jinja_executions_aux begin

definition start_heap_obs :: "(thread_id \<times> obs_event action) list"
  where "start_heap_obs = lift_start_obs start_tid start_heap_obs'"

lemma start_heap_obs_not_Read: "(t, NormalAction (ReadMem ad al v)) \<notin> set start_heap_obs"
using start_heap_obs'_not_Read[of ad al v] by(auto simp add: start_heap_obs_def)

lemma thread_start_actions_ok_init_fin:
  assumes E: "E \<in> if.\<E> start_state"
  shows "thread_start_actions_ok (lappend (llist_of start_heap_obs) E)"
  (is "thread_start_actions_ok ?E")
proof(rule thread_start_actions_okI)
  fix a
  assume a: "a \<in> actions ?E"
    and a_new: "\<not> is_new_action (action_obs ?E a)"
  show "\<exists>i. i \<le> a \<and> action_obs ?E i = InitialThreadAction \<and> action_tid ?E i = action_tid ?E a"
  proof(cases "action_tid ?E a = start_tid")
    case True thus ?thesis
      by(auto simp add: lift_start_obs_def action_tid_def action_obs_def lnth_lappend1 lnth_LCons start_heap_obs_def split: nat.split)
  next
    case False

    let ?a = "a - length start_heap_obs"

    from False have "a \<ge> length start_heap_obs"
      by(rule contrapos_np)(auto simp add: lift_start_obs_def start_heap_obs_def action_tid_def lnth_LCons lnth_lappend1 split: nat.split)
    hence [simp]: "action_tid ?E a = action_tid E ?a" "action_obs ?E a = action_obs E ?a"
      by(simp_all add: action_tid_def lnth_lappend2 action_obs_def)

    from False have not_running: "\<And>x ln. thr start_state (action_tid E ?a) \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
      by(rule contrapos_nn)(auto dest: thr_start_state_RunningD)
    
    from E obtain E' where E': "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and \<tau>Runs: "if.mthr.\<tau>Runs start_state E'"
      by(rule if.\<E>.cases)
    from a E' `a \<ge> length start_heap_obs`
    have Fin_a: "Fin ?a < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))"
      by(cases "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))")(auto simp add: actions_def)
    with \<tau>Runs obtain m n t ta
    where a_obs: "lnth (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))) (a - length start_heap_obs) = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
      and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" 
      and m: "Fin m < tlength E'"
      and a_conv: "?a = (\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
      and E'_m: "tnth E' m = (t, ta)"
      by(rule if.actions_\<E>E_aux)
    from a_obs have [simp]: "action_tid E ?a = t" "action_obs E ?a = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n"
      by(simp_all add: E' action_tid_def action_obs_def)

    let ?E' = "tdropn (Suc m) E'"
    let ?m_E' = "ltake (Fin m) (llist_of_tllist E')"
    have E'_unfold: "E' = lappendt (ltake (Fin m) (llist_of_tllist E')) (TCons (tnth E' m) ?E')"
      unfolding tdropn_Suc_conv_tdropn[OF m] lappendt_ltake_tdropn ..
    hence "if.mthr.\<tau>Runs start_state (lappendt ?m_E' (TCons (tnth E' m) ?E'))"
      using \<tau>Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "if.mthr.\<tau>rtrancl3p start_state (list_of ?m_E') \<sigma>'"
      and \<tau>Runs': "if.mthr.\<tau>Runs \<sigma>' (TCons (tnth E' m) ?E')"
      by(rule if.mthr.\<tau>Runs_lappendtE) simp
    from \<tau>Runs' obtain \<sigma>'' \<sigma>''' where \<sigma>'_\<sigma>'': "if.mthr.silent_moves \<sigma>' \<sigma>''"
      and red_a: "if.redT \<sigma>'' (t, ta) \<sigma>'''"
      and n\<tau>: "\<not> if.m\<tau>move \<sigma>'' (t, ta) \<sigma>'''"
      and \<tau>Runs'': "if.mthr.\<tau>Runs \<sigma>''' ?E'"
      unfolding E'_m by cases
    from red_a obtain status x ln where tst: "thr \<sigma>'' t = \<lfloor>((status, x), ln)\<rfloor>" by cases auto
    show ?thesis
    proof(cases "status = PreStart \<or> status = Finished")
      case True
      from start_state_Status_no_wait_locks \<sigma>_\<sigma>' have "Status_no_wait_locks (thr \<sigma>')"
        by(rule init_fin_\<tau>rtrancl3p_preserve_Status_no_wait_locks)
      hence "Status_no_wait_locks (thr \<sigma>'')" using \<sigma>'_\<sigma>''
        by(rule init_fin_silent_moves_preserve_Status_no_wait_locks)
      with True tst have "ln = no_wait_locks"
        by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      with red_a tst True have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [InitialThreadAction]" by(cases) auto
      hence "action_obs E ?a = InitialThreadAction" using a_obs n unfolding E'
        by(simp add: action_obs_def)
      thus ?thesis by(auto)
    next
      case False
      hence "status = Running" by(cases status) auto
      with tst init_fin_silent_moves_Running_invariant[OF \<sigma>'_\<sigma>'', of t]
        init_fin_\<tau>rtrancl3p_Running_InitialThreadAction[OF \<sigma>_\<sigma>' not_running]
      have "(action_tid E ?a, \<epsilon>\<lbrace>\<^bsub>o\<^esub> InitialThreadAction\<rbrace>) \<in> set (list_of (ltake (Fin m) (llist_of_tllist E')))"
        using a_obs E' by(auto simp add: action_tid_def)
      then obtain i where "i < m" "Fin i < tlength E'" 
        and nth_i: "tnth E' i = (action_tid E ?a, \<epsilon>\<lbrace>\<^bsub>o\<^esub> InitialThreadAction\<rbrace>)"
        unfolding in_set_conv_nth 
        by(cases "tlength E'")(auto simp add: length_list_of_conv_the_Fin lnth_ltake)

      let ?i' = "\<Sum>i<i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>"
      let ?i = "length start_heap_obs + ?i'"

      from `i < m` have "(\<Sum>i<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = ?i' + (\<Sum>i=i..<m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
      hence "?i' \<le> ?a" unfolding a_conv by simp
      hence "?i \<le> a" using `a \<ge> length start_heap_obs` by arith


      from `?i' \<le> ?a` have "Fin ?i' < llength E" using Fin_a E'
        by(simp add: le_less_trans[where y="Fin ?a"])
      from lnth_lconcat_conv[OF this[unfolded E'], folded E']
      obtain k l 
        where nth_i': "lnth E ?i' = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) k) l"
        and l: "l < length \<lbrace>snd (tnth E' k)\<rbrace>\<^bsub>o\<^esub>"
        and k: "Fin k < tlength E'"
        and i_conv: "Fin ?i' = (\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin l"
        by(fastsimp simp add: split_beta)

      have "(\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) =
            (\<Sum>i<k. (Fin \<circ> (\<lambda>i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(rule setsum_cong)(simp_all add: less_trans[where y="Fin k"] split_beta k)
      also have "\<dots> = Fin (\<Sum>i<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_inat_def)
      finally have i_conv: "?i' = (\<Sum>i<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + l" using i_conv by simp

      have [simp]: "i = k"
      proof(rule ccontr)
        assume "i \<noteq> k"
        thus False unfolding neq_iff
        proof
          assume "i < k"
          hence "(\<Sum>i<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=i..<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with i_conv have "(\<Sum>i=i..<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" "l = 0" by simp_all
          moreover have "(\<Sum>i=i..<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `i < k`]) simp
          ultimately show False using nth_i by simp
        next
          assume "k < i"
          hence "?i' = (\<Sum>i<k. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=k..<i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with i_conv have "(\<Sum>i=k..<i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" by simp
          moreover have "(\<Sum>i=k..<i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' k)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `k < i`]) simp
          ultimately show False using l by simp
        qed
      qed
      with l nth_i have [simp]: "l = 0" by simp
      
      hence "lnth E ?i' = (action_tid E ?a, InitialThreadAction)"
        using nth_i nth_i' k by simp
      with `?i \<le> a` show ?thesis
        by(auto simp add: action_tid_def action_obs_def lnth_lappend2)
    qed
  qed
qed

lemma executions:
  assumes cut_and_update: "cut_and_update start_state (mrw_values P empty (map snd start_heap_obs))"
  shows "executions (lappend (llist_of start_heap_obs) ` if.\<E> start_state) P"
  (is "executions ?\<E> _")
proof -
  let ?n = "length start_heap_obs"
  let ?\<E>' = "lappend (llist_of (lift_start_obs start_tid start_heap_obs')) ` if.\<E> start_state"

  show ?thesis unfolding start_heap_obs_def
  proof
    fix E ws r
    assume E: "E \<in> ?\<E>'"
      and wf: "P \<turnstile> (E, ws) \<surd>"
      and mrw: "\<And>a. \<lbrakk> a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
    show "\<exists>E'\<in>?\<E>'. \<exists>ws'. P \<turnstile> (E', ws') \<surd> \<and> ltake (Fin r) E = ltake (Fin r) E' \<and>
                           sequentially_consistent P (E', ws') \<and>
                           action_tid E r = action_tid E' r \<and> action_obs E r \<approx> action_obs E' r \<and>
                           (r \<in> actions E \<longrightarrow> r \<in> actions E')"
    proof(cases "\<exists>r'. r' \<in> read_actions E \<and> r \<le> r'")
      case False
      have "sequentially_consistent P (E, ws)"
      proof(rule sequentially_consistentI)
        fix a
        assume "a \<in> read_actions E"
        with False have "a < r" by auto
        thus "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw)
      qed
      moreover have "action_obs E r \<approx> action_obs E r" by(rule sim_action_refl)
      ultimately show ?thesis using wf E by blast
    next
      case True
      let ?P = "\<lambda>r'. r' \<in> read_actions E \<and> r \<le> r'"
      let ?r = "Least ?P"
      from True obtain r' where r': "?P r'" by blast
      hence r: "?P ?r" by(rule LeastI)
      {
        fix a
        assume "a < ?r" "a \<in> read_actions E"
        have "P,E \<turnstile> a \<leadsto>mrw ws a"
        proof(cases "a < r")
          case True
          thus ?thesis using `a \<in> read_actions E` by(rule mrw)
        next
          case False
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `a < ?r` have False by simp
          thus ?thesis ..
        qed }
      note mrw' = this

      from E obtain E' E'' where E: "E = lappend (llist_of start_heap_obs) E''"
        and E'': "E'' \<in> if.\<E> start_state" unfolding start_heap_obs_def  by auto

      from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
        and \<tau>Runs: "if.mthr.\<tau>Runs start_state E'"
        by(rule if.\<E>.cases)

      have r_len: "length start_heap_obs \<le> ?r"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?r < length start_heap_obs" by simp
        moreover with r E obtain t ad al v where "start_heap_obs ! ?r = (t, NormalAction (ReadMem ad al v))"
          by(cases "start_heap_obs ! ?r")(fastsimp elim!: read_actions.cases simp add: actions_def action_obs_def lnth_lappend1)
        ultimately have "(t, NormalAction (ReadMem ad al v)) \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
        thus False by(auto simp add: start_heap_obs_not_Read)
      qed
      let ?n = "length start_heap_obs"
      from r r_len E have r: "?r - ?n \<in> read_actions E''"
        by(fastsimp elim!: read_actions.cases simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)
      
      from r have "?r - ?n \<in> actions E''" by(auto)
      hence "Fin (?r - ?n) < llength E''" by(rule actionsE)
      with \<tau>Runs obtain r_m r_n t_r ta_r 
        where E_r: "lnth E'' (?r - ?n) = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
        and r_n: "r_n < length \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and r_m: "Fin r_m < tlength E'"
        and r_conv: "?r - ?n = (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n"
        and E'_r_m: "tnth E' r_m = (t_r, ta_r)"
        unfolding E' by(rule if.actions_\<E>E_aux)

      let ?E' = "tdropn (Suc r_m) E'"
      let ?r_m_E' = "ltake (Fin r_m) (llist_of_tllist E')"
      have E'_unfold: "E' = lappendt (ltake (Fin r_m) (llist_of_tllist E')) (TCons (tnth E' r_m) ?E')"
        unfolding tdropn_Suc_conv_tdropn[OF r_m] lappendt_ltake_tdropn ..
      hence "if.mthr.\<tau>Runs start_state (lappendt ?r_m_E' (TCons (tnth E' r_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "if.mthr.\<tau>rtrancl3p start_state (list_of ?r_m_E') \<sigma>'"
        and \<tau>Runs': "if.mthr.\<tau>Runs \<sigma>' (TCons (tnth E' r_m) ?E')"
        by(rule if.mthr.\<tau>Runs_lappendtE) simp
      from \<tau>Runs' obtain \<sigma>'' \<sigma>''' where \<sigma>'_\<sigma>'': "if.mthr.silent_moves \<sigma>' \<sigma>''"
        and red_ra: "if.redT \<sigma>'' (t_r, ta_r) \<sigma>'''"
        and n\<tau>: "\<not> if.m\<tau>move \<sigma>'' (t_r, ta_r) \<sigma>'''"
        and \<tau>Runs'': "if.mthr.\<tau>Runs \<sigma>''' ?E'"
        unfolding E'_r_m by cases

      note \<sigma>_\<sigma>'
      also note if.mthr.silent_moves_into_\<tau>rtrancl3p[OF \<sigma>'_\<sigma>'']
      finally have \<sigma>_\<sigma>'': "if.mthr.\<tau>rtrancl3p start_state (list_of ?r_m_E') \<sigma>''" by simp

      let ?vs = "mrw_values P empty (map snd start_heap_obs)"
      { fix a
        assume "Fin a < Fin ?r"
          and "a \<in> read_actions E"
        have "a < r"
        proof(rule ccontr)
          assume "\<not> a < r"
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `Fin a < Fin ?r` show False by simp
        qed
        hence "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw) }
      with `E \<in> ?\<E>'` wf have "ta_seq_consist P empty (lmap snd (ltake (Fin ?r) E))"
        unfolding start_heap_obs_def by(rule jmm.ta_seq_consist_mrwI)

      hence start_sc: "ta_seq_consist P empty (llist_of (map snd start_heap_obs))"
        and "ta_seq_consist P ?vs (lmap snd (ltake (Fin (?r - ?n)) E''))"
        using `?n \<le> ?r` unfolding E ltake_lappend lmap_lappend_distrib
        by(simp_all add: ta_seq_consist_lappend o_def)

      note this(2) also from r_m
      have r_m_sum_len_eq: "(\<Sum>i<r_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) = Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(subst setsum_hom[symmetric, where f=Fin])(auto simp add: zero_inat_def split_def less_trans[where y="Fin r_m"] intro: setsum_cong)
      hence "ltake (Fin (?r - ?n)) E'' = 
            lappend (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')) 
                    (ltake (Fin r_n) (ldrop (Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E''))"
        unfolding ltake_lmap[symmetric] lconcat_ltake r_conv plus_inat_simps(1)[symmetric] ltake_plus_conv_lappend
        unfolding E' by simp
      finally have "ta_seq_consist P ?vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')))"
        and sc_ta_r: "ta_seq_consist P (mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))) (lmap snd (ltake (Fin r_n) (ldropn (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'')))"
        unfolding lmap_lappend_distrib by(simp_all add: ta_seq_consist_lappend split_def)
      note this(1) also
      have "lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (Fin r_m) (llist_of_tllist E'))))
            = llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E')))"
        unfolding lmap_lconcat lmap_compose[symmetric] o_def split_def lconcat_llist_of[symmetric] map_map lmap_llist_of[symmetric]
        by simp
      finally have "ta_seq_consist P ?vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))" .
      from sequential_completion[OF cut_and_update ta_seq_consist_convert_RA \<sigma>_\<sigma>'' this red_ra n\<tau>]
      obtain ta' ttas' 
        where "if.mthr.\<tau>Runs \<sigma>'' (TCons (t_r, ta') ttas')"
        and sc: "ta_seq_consist P (mrw_values P empty (map snd start_heap_obs)) 
                   (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') (llist_of_tllist ttas')))))"
          and eq_ta: "eq_upto_seq_inconsist P \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P ?vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))"
          by blast

      let ?E_sc' = "lappendt (llist_of (list_of ?r_m_E')) (TCons (t_r, ta') ttas')"
      let ?E_sc'' = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist ?E_sc'))"
      let ?E_sc = "lappend (llist_of start_heap_obs) ?E_sc''"

      from \<sigma>_\<sigma>'' `if.mthr.\<tau>Runs \<sigma>'' (TCons (t_r, ta') ttas')`
      have "if.mthr.\<tau>Runs start_state ?E_sc'" 
        by(rule if.mthr.\<tau>rtrancl3p_into_\<tau>Runs)
      hence "?E_sc'' \<in> if.\<E> start_state" by(rule if.\<E>.intros)
      hence "?E_sc \<in> ?\<E>" by(rule imageI)
      moreover from `?E_sc'' \<in> if.\<E> start_state`
      have tsa_ok: "thread_start_actions_ok ?E_sc"
        by(rule thread_start_actions_ok_init_fin) 
        
      from sc have "ta_seq_consist P empty (lmap snd ?E_sc)"
        by(simp add: lmap_lappend_distrib o_def lmap_lconcat lmap_compose[symmetric] split_def ta_seq_consist_lappend start_sc del: lmap_compose)
      from jmm.ta_seq_consist_imp_sequentially_consistent[OF `?E_sc \<in> ?\<E>`[unfolded start_heap_obs_def] tsa_ok[unfolded start_heap_obs_def] this[unfolded start_heap_obs_def]]
      obtain ws_sc where "sequentially_consistent P (?E_sc, ws_sc)"
        and "P \<turnstile> (?E_sc, ws_sc) \<surd>" unfolding start_heap_obs_def[symmetric] by blast
      moreover {
        have Fin_sum_r_m_eq: "Fin (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))"
          by(auto intro: setsum_cong simp add: less_trans[OF _ r_m] lnth_ltake llength_lconcat_lfinite_conv_sum setsum_hom[symmetric, where f=Fin] zero_inat_def[symmetric] split_beta)
        also have "\<dots> \<le> llength E''" unfolding E'
          by(blast intro: lprefix_llength_le lprefix_lconcatI lmap_lprefix)
        finally have r_m_E: "ltake (Fin (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>))) E = ltake (Fin (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>))) ?E_sc"
          by(simp add: ltake_lappend lappend_eq_lappend_conv lmap_lappend_distrib r_m_sum_len_eq ltake_lmap[symmetric] min_def zero_inat_def[symmetric] E E' lconcat_ltake ltake_all del: ltake_lmap)

        have drop_r_m_E: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E = lappend (llist_of (map (Pair t_r) \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ldropn (Suc r_m) (llist_of_tllist E'))))"
          (is "_ = ?drop_r_m_E") using E'_r_m unfolding E E'
          by(subst (2) E'_unfold)(simp add: ldropn_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric])

        have drop_r_m_E_sc: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) ?E_sc =
          lappend (llist_of (map (Pair t_r) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist ttas')))"
          by(simp add: ldropn_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric])

        let ?vs_r_m = "mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))"
        note sc_ta_r also
        from drop_r_m_E have "ldropn (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'' = ?drop_r_m_E"
          unfolding E by(simp add: ldropn_lappend2)
        also have "lmap snd (ltake (Fin r_n) \<dots>) = llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)" using r_n
          by(simp add: ltake_lappend lmap_lappend_distrib ltake_lmap[symmetric] take_map o_def zero_inat_def[symmetric] del: ltake_lmap)
        finally have sc_ta_r: "ta_seq_consist P ?vs_r_m (llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))" .
        note eq_ta
        also have "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" by simp
        finally have "eq_upto_seq_inconsist P (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs_r_m"
          by(simp add: list_of_lconcat split_def o_def map_concat)
        from eq_upto_seq_inconsist_appendD[OF this sc_ta_r]
        have r_n': "r_n \<le> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
          and take_r_n_eq: "take r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
          and eq_r_n: "eq_upto_seq_inconsist P (drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) (drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (mrw_values P ?vs_r_m (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"
          using r_n by(simp_all add: min_def)
        from r_conv `?n \<le> ?r` have r_conv': "?r = (?n + (\<Sum>i<r_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) + r_n" by simp
        from r_n' r_n take_r_n_eq r_m_E drop_r_m_E drop_r_m_E_sc
        have take_r'_eq: "ltake (Fin ?r) E = ltake (Fin ?r) ?E_sc" unfolding r_conv'
          apply(subst (1 2) plus_inat_simps(1)[symmetric])
          apply(subst (1 2) ltake_plus_conv_lappend)
          apply(simp add: lappend_eq_lappend_conv ltake_lappend1 take_map)
          done
        hence take_r_eq: "ltake (Fin r) E = ltake (Fin r) ?E_sc"
          by(rule ltake_eq_ltake_antimono)(simp add: `?P ?r`)
        
        from eq_r_n nth_drop'[OF r_n, symmetric]
        have "drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<noteq> []" by(auto simp add: eq_upto_seq_inconsist_simps)
        hence r_n': "r_n < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by simp
        hence eq_r_n: "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n \<approx> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n"
          using eq_r_n nth_drop'[OF r_n, symmetric] nth_drop'[OF r_n', symmetric]
          by(simp add: eq_upto_seq_inconsist_simps split: action.split_asm obs_event.split_asm split_if_asm)
        obtain tid_eq: "action_tid E r = action_tid ?E_sc r" 
          and obs_eq: "action_obs E r \<approx> action_obs ?E_sc r"
        proof(cases "r < ?r")
          case True
          { from True have "action_tid E r = action_tid (ltake (Fin ?r) E) r"
              by(simp add: action_tid_def lnth_ltake)
            also note take_r'_eq
            also have "action_tid (ltake (Fin ?r) ?E_sc) r = action_tid ?E_sc r"
              using True by(simp add: action_tid_def lnth_ltake)
            finally have "action_tid E r = action_tid ?E_sc r" . }
          moreover
          { from True have "action_obs E r = action_obs (ltake (Fin ?r) E) r"
              by(simp add: action_obs_def lnth_ltake)
            also note take_r'_eq
            also have "action_obs (ltake (Fin ?r) ?E_sc) r = action_obs ?E_sc r"
              using True by(simp add: action_obs_def lnth_ltake)
            finally have "action_obs E r \<approx> action_obs ?E_sc r" by simp }
          ultimately show thesis by(rule that)
        next
          case False
          with `?P ?r` have r_eq: "r = ?r" by simp
          hence "lnth E r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)" using E_r r_conv' E by(simp add: lnth_lappend2)
          moreover have "lnth ?E_sc r = (t_r, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n)" using `?n \<le> ?r` r_n'
            by(subst r_eq)(simp add: r_conv lnth_lappend2 lmap_lappend_distrib Fin_sum_r_m_eq[symmetric] lnth_lappend1)
          ultimately have "action_tid E r = action_tid ?E_sc r" "action_obs E r \<approx> action_obs ?E_sc r"
            using eq_r_n by(simp_all add: action_tid_def action_obs_def)
          thus thesis by(rule that)
        qed
        
        have "Fin r < Fin ?n + llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil))))"
          using `?P ?r` r_n' unfolding lmap_lappend_distrib
          by(simp add: lconcat_lappend Fin_sum_r_m_eq[symmetric] r_conv')
        also have "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil)))) \<le> llength ?E_sc''"
          by(rule lprefix_llength_le[OF lprefix_lconcatI])(simp add: lmap_lprefix)
        finally have "r \<in> actions ?E_sc" by(simp add: actions_def add_left_mono)
        note this tid_eq obs_eq take_r_eq }
      ultimately show ?thesis unfolding start_heap_obs_def by blast
    qed
  qed(rule jmm.\<E>_new_actions_for_fun)
qed

end



locale heap_jmm_aux =
  heap empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write + 
  mthr!: \<tau>multithreaded_wf final r convert_RA \<tau>move +
  wfix!: lifting_inv final r convert_RA wfx wfix 
  for empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and final :: "'x \<Rightarrow> bool"
  and r :: "(addr, thread_id, 'x, 'heap, addr, obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and \<tau>move :: "(addr, thread_id, 'x, 'heap, addr, obs_event) \<tau>moves" 
  and wfx :: "thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and wfix :: "'i \<Rightarrow> thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  +
  fixes P :: "'md prog"
  assumes red_hext_incr: "t \<turnstile> (x, m) -ta\<rightarrow> (x', m') \<Longrightarrow> m \<unlhd> m'"
  and red_New_typeof_addrD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr m ad = None \<and> typeof_addr m' ad = Some (ty_of_htype CTn)"
  and red_New_same_addr_same:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
  and red_created_object:
  "\<lbrakk> heap_ops_typeof_minimal; t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); typeof_addr m' a = \<lfloor>T\<rfloor>; typeof_addr m a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> m' \<turnstile>a a : CTn"
  and red_read_typeable:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; wfix I t x m; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,m \<turnstile> ad@al : T'"

sublocale heap_jmm_aux < mthr!: if_\<tau>multithreaded_wf final r convert_RA \<tau>move
by(unfold_locales)

sublocale heap_jmm_aux < wfix_if!: if_lifting_inv final r convert_RA wfx wfix
by(unfold_locales)

sublocale heap_jmm_aux < wfix_if!: \<tau>lifting_inv
  mthr.init_fin_final
  mthr.init_fin
  "map NormalAction \<circ> convert_RA"
  mthr.init_fin_\<tau>move
  "init_fin_lift wfx"
  "init_fin_lift_inv wfix"
by(unfold_locales)

context heap_jmm_aux begin

lemma heap_jmm_aux_wfix_mono:
  assumes inv: "lifting_inv r wfx' wfix'"
  and mono: "\<And>I t x m. \<lbrakk> wfx' t x m; wfix' I t x m \<rbrakk> \<Longrightarrow> \<exists>I'. wfx t x m \<and> wfix I' t x m"
  shows "heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_write final r \<tau>move wfx' wfix' P"
proof -
  interpret wfix'!: lifting_inv final r convert_RA wfx' wfix' by(rule inv)
  show ?thesis
    by(unfold_locales)(blast intro: red_hext_incr red_New_same_addr_same red_created_object red_read_typeable dest: red_New_typeof_addrD mono)+
qed

lemma init_fin_hext:
  "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m') \<Longrightarrow> m \<unlhd> m'"
by(cases rule: mthr.init_fin.cases)(auto dest: red_hext_incr)

lemma init_fin_redT_hext:
  assumes "mthr.if.redT \<sigma> (t, ta) \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by cases(auto dest: init_fin_hext)

lemma init_fin_silent_moves_hext:
  assumes "mthr.if.mthr.silent_moves \<sigma> \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by induct(auto dest!: init_fin_redT_hext elim: hext_trans)

lemma init_fin_\<tau>rtrancl3p_hext:
  assumes "mthr.if.mthr.\<tau>rtrancl3p \<sigma> ttas \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by induct(auto dest!: init_fin_redT_hext elim: hext_trans)

lemma \<E>_new_actions_for_unique:
  assumes E: "E \<in> lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` mthr.if.\<E> (start_state f P C M vs)"
  and a: "a \<in> new_actions_for P E adal"
  and a': "a' \<in> new_actions_for P E adal"
  shows "a = a'"
using a a'
proof(induct a a' rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le a a')
  note a = `a \<in> new_actions_for P E adal`
    and a' = `a' \<in> new_actions_for P E adal`
    and a_a' = `a \<le> a'`
  obtain ad al where adal: "adal = (ad, al)" by(cases adal)

  let ?init_obs = "lift_start_obs start_tid start_heap_obs"
  have distinct: "distinct (filter (\<lambda>obs. \<exists>a CTn. obs = NormalAction (NewHeapElem a CTn)) (map snd ?init_obs))"
    unfolding start_heap_obs_def
    by(fastsimp intro: inj_onI intro!: distinct_filter simp add: distinct_map distinct_zipI1 distinct_initialization_list)

  from dom_typeof_addr_start_heap
  have dom_start_state: "{a. \<exists>CTn. NormalAction (NewHeapElem a CTn) \<in> snd ` set ?init_obs} \<subseteq> dom (typeof_addr (shr (start_state f P C M vs)))"
    by(fastsimp simp add: init_fin_lift_state_conv_simps shr_start_state dest: NewHeapElem_start_heap_obs_start_addrsD subsetD)
  
  show ?case
  proof(cases "a' < length ?init_obs")
    case True
    with a' adal E obtain t_a' CTn_a'
      where CTn_a': "?init_obs ! a' = (t_a', NormalAction (NewHeapElem ad CTn_a'))"
      by(cases "?init_obs ! a'")(fastsimp elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from True a_a' have len_a: "a < length ?init_obs" by simp
    with a adal E obtain t_a CTn_a
      where CTn_a: "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
      by(cases "?init_obs ! a")(fastsimp elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from CTn_a CTn_a' True len_a
    have "NormalAction (NewHeapElem ad CTn_a') \<in> snd ` set ?init_obs"
      and "NormalAction (NewHeapElem ad CTn_a) \<in> snd ` set ?init_obs" unfolding set_conv_nth
      by(fastsimp intro: rev_image_eqI)+
    hence [simp]: "CTn_a' = CTn_a" using distinct_start_addrs
      by(auto simp add: in_set_conv_nth distinct_conv_nth start_heap_obs_def start_addrs_def) blast
    from distinct_filterD[OF distinct, of a' a "NormalAction (NewHeapElem ad CTn_a)"] len_a True CTn_a CTn_a'
    show "a = a'" by simp
  next
    case False
    obtain n where n: "length ?init_obs = n" by blast
    with False have "n \<le> a'" by simp
    
    from E obtain E'' where E: "E = lappend (llist_of ?init_obs) E''"
      and E'': "E'' \<in> mthr.if.\<E> (start_state f P C M vs)" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and \<tau>Runs: "mthr.if.mthr.\<tau>Runs (start_state f P C M vs) E'" by(rule mthr.if.\<E>.cases)
    
    from E E'' a' n `n \<le> a'` adal have a': "a' - n \<in> new_actions_for P E'' adal"
      by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)
    
    from a' have "a' - n \<in> actions E''" by(auto elim: new_actionsE)
    hence "Fin (a' - n) < llength E''" by(rule actionsE)
    with \<tau>Runs obtain a'_m a'_n t_a' ta_a'
      where E_a': "lnth E'' (a' - n) = (t_a', \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n)"
      and a'_n: "a'_n < length \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>" and a'_m: "Fin a'_m < tlength E'"
      and a'_conv: "a' - n = (\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a'_n"
      and E'_a'_m: "tnth E' a'_m = (t_a', ta_a')"
      unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
    from a' have "is_new_action (action_obs E'' (a' - n))"
      and "(ad, al) \<in> action_loc P E'' (a' - n)"
      unfolding adal by(auto elim: new_actionsE)
    then obtain CTn'
      where "action_obs E'' (a' - n) = NormalAction (NewHeapElem ad CTn')"
      by cases(fastsimp)+
    hence New_ta_a': "\<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NormalAction (NewHeapElem ad CTn')"
      using E_a' a'_n unfolding action_obs_def by simp
    
    show ?thesis
    proof(cases "a < n")
      case True
      with a adal E n obtain t_a CTn_a where "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
        by(cases "?init_obs ! a")(fastsimp elim!: is_new_action.cases simp add: action_obs_def lnth_lappend1 new_actions_for_def)+

      with subsetD[OF dom_start_state, of ad] n True
      have a_shr_\<sigma>: "ad \<in> dom (typeof_addr (shr (start_state f P C M vs)))"
        by(fastsimp simp add: set_conv_nth intro: rev_image_eqI)
      then obtain T where T: "typeof_addr (shr (start_state f P C M vs)) ad = \<lfloor>T\<rfloor>" by auto
      
      have E'_unfold': "E' = lappendt (ltake (Fin a'_m) (llist_of_tllist E')) (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E'))"
        unfolding tdropn_Suc_conv_tdropn[OF a'_m] lappendt_ltake_tdropn ..
      hence "mthr.if.mthr.\<tau>Runs (start_state f P C M vs) (lappendt (ltake (Fin a'_m) (llist_of_tllist E')) (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E')))"
        using \<tau>Runs by simp
      then obtain \<sigma>'
        where \<sigma>_\<sigma>': "mthr.if.mthr.\<tau>rtrancl3p (start_state f P C M vs) (list_of (ltake (Fin a'_m) (llist_of_tllist E'))) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.\<tau>Runs \<sigma>' (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E'))"
        by(rule mthr.if.mthr.\<tau>Runs_lappendtE) simp
      from \<tau>Runs' obtain \<sigma>'' \<sigma>'''
        where \<sigma>'_\<sigma>'': "mthr.if.mthr.silent_moves \<sigma>' \<sigma>''"
        and red_a': "mthr.if.redT \<sigma>'' (t_a', ta_a') \<sigma>'''"
        and "\<not> mthr.if.m\<tau>move \<sigma>'' (t_a', ta_a') \<sigma>'''"
        and \<tau>Runs'': "mthr.if.mthr.\<tau>Runs \<sigma>''' (tdropn (Suc a'_m) E')"
        unfolding E'_a'_m by cases
      from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a' obtain x_a' x'_a' m'_a' 
        where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>'') ta_a' (x'_a', m'_a')"
        and \<sigma>''': "redT_upd \<sigma>'' t_a' ta_a' x'_a' m'_a' \<sigma>'''"
        and ts_t_a': "thr \<sigma>'' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a' X_a' X'_a'
        where x_a': "x_a' = (Running, X_a')"
        and x'_a': "x'_a' = (Running, X'_a')"
        and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
        and red''_a': "t_a' \<turnstile> \<langle>X_a', shr \<sigma>''\<rangle> -ta'_a'\<rightarrow> \<langle>X'_a', m'_a'\<rangle>"
        by cases fastsimp+
      from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
        and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a' have typeof_ad': "typeof_addr (shr \<sigma>'') ad = None"
        by(auto dest: red_New_typeof_addrD)
      
      have "shr (start_state f P C M vs) \<unlhd> shr \<sigma>'" using \<sigma>_\<sigma>' by(rule init_fin_\<tau>rtrancl3p_hext)
      also from \<sigma>'_\<sigma>'' have "shr \<sigma>' \<unlhd> shr \<sigma>''" by(rule init_fin_silent_moves_hext)
      finally have "typeof_addr (shr \<sigma>'') ad = \<lfloor>T\<rfloor>" using T by(auto dest: typeof_addr_hext_mono)
      with typeof_ad' have False by simp
      thus ?thesis ..
    next
      case False
      hence "n \<le> a" by simp

      from E E'' a n `n \<le> a` adal have a: "a - n \<in> new_actions_for P E'' adal"
        by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)

      from a have "a - n \<in> actions E''" by(auto elim: new_actionsE)
      hence "Fin (a - n) < llength E''" by(rule actionsE)


      with \<tau>Runs obtain a_m a_n t_a ta_a 
        where E_a: "lnth E'' (a - n) = (t_a, \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n)"
        and a_n: "a_n < length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>" and a_m: "Fin a_m < tlength E'"
        and a_conv: "a - n = (\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a_n"
        and E'_a_m: "tnth E' a_m = (t_a, ta_a)"
        unfolding E' by(rule mthr.if.actions_\<E>E_aux)
  
      from a have "is_new_action (action_obs E'' (a - n))" 
        and "(ad, al) \<in> action_loc P E'' (a - n)" 
        unfolding adal by(auto elim: new_actionsE)
      then obtain CTn where "action_obs E'' (a - n) = NormalAction (NewHeapElem ad CTn)"
        by cases(fastsimp)+
      hence New_ta_a: " \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NormalAction (NewHeapElem ad CTn)"
        using E_a a_n unfolding action_obs_def by simp
      
      let ?E' = "tdropn (Suc a_m) E'"
  
      have E'_unfold: "E' = lappendt (ltake (Fin a_m) (llist_of_tllist E')) (TCons (tnth E' a_m) ?E')"
        unfolding tdropn_Suc_conv_tdropn[OF a_m] lappendt_ltake_tdropn ..
      hence "mthr.if.mthr.\<tau>Runs (start_state f P C M vs) (lappendt (ltake (Fin a_m) (llist_of_tllist E')) (TCons (tnth E' a_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.\<tau>rtrancl3p (start_state f P C M vs) (list_of (ltake (Fin a_m) (llist_of_tllist E'))) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.\<tau>Runs \<sigma>' (TCons (tnth E' a_m) ?E')"
        by(rule mthr.if.mthr.\<tau>Runs_lappendtE) simp
      from \<tau>Runs' obtain \<sigma>'' \<sigma>''' where "mthr.if.mthr.silent_moves \<sigma>' \<sigma>''"
        and red_a: "mthr.if.redT \<sigma>'' (t_a, ta_a) \<sigma>'''"
        and "\<not> mthr.if.m\<tau>move \<sigma>'' (t_a, ta_a) \<sigma>'''"
        and \<tau>Runs'': "mthr.if.mthr.\<tau>Runs \<sigma>''' ?E'"
        unfolding E'_a_m by cases
      from New_ta_a a_n have "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a obtain x_a x'_a m'_a 
        where red'_a: "mthr.init_fin t_a (x_a, shr \<sigma>'') ta_a (x'_a, m'_a)"
        and \<sigma>''': "redT_upd \<sigma>'' t_a ta_a x'_a m'_a \<sigma>'''"
        and ts_t_a: "thr \<sigma>'' t_a = \<lfloor>(x_a, no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a X_a X'_a
        where x_a: "x_a = (Running, X_a)"
        and x'_a: "x'_a = (Running, X'_a)"
        and ta_a: "ta_a = convert_TA_initial (convert_obs_initial ta'_a)"
        and red''_a: "t_a \<turnstile> (X_a, shr \<sigma>'') -ta'_a\<rightarrow> (X'_a, m'_a)"
        by cases fastsimp+
      from ta_a New_ta_a a_n have New_ta'_a: "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NewHeapElem ad CTn"
        and a_n': "a_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn \<in> set \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a have typeof_m'_a_ad: "typeof_addr m'_a ad \<noteq> None"
        by(auto dest: red_New_typeof_addrD)
      
      have "a_m \<le> a'_m"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "a'_m < a_m" by simp
        hence "(\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a'_m..<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          by(simp add: setsum_upto_add_nat)
        hence "a' - n < a - n" using `a'_m < a_m` a'_n E'_a'_m unfolding a_conv a'_conv
          by(subst (asm) setsum_head_upt_Suc) simp_all
        with a_a' show False by simp
      qed
  
      have a'_less: "a' - n < (a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence a'_greater: "(a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> \<le> a' - n" by simp
        
        have "a_m < a'_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          with `a_m \<le> a'_m` have "a_m = a'_m" by simp
          with a'_greater a_n a'_n E'_a'_m E'_a_m show False
            unfolding a_conv a'_conv by simp
        qed
        hence a'_m_a_m: "Fin (a'_m - Suc a_m) < tlength ?E'" using a'_m
          by(cases "tlength E'") simp_all
        from `a_m < a'_m` a'_m E'_a'_m
        have E'_a'_m': "tnth ?E' (a'_m - Suc a_m) = (t_a', ta_a')" by simp
    
        have E'_unfold': "?E' = lappendt (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E')) (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E'))"
          unfolding tdropn_Suc_conv_tdropn[OF a'_m_a_m] lappendt_ltake_tdropn ..
        hence "mthr.if.mthr.\<tau>Runs \<sigma>''' (lappendt (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E')) (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E')))"
          using \<tau>Runs'' by simp
        then obtain \<sigma>''''
          where \<sigma>'''_\<sigma>'''': "mthr.if.mthr.\<tau>rtrancl3p \<sigma>''' (list_of (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E'))) \<sigma>''''"
          and \<tau>Runs''': "mthr.if.mthr.\<tau>Runs \<sigma>'''' (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E'))"
          by(rule mthr.if.mthr.\<tau>Runs_lappendtE) simp
        from \<tau>Runs''' obtain \<sigma>''''' \<sigma>''''''
          where \<sigma>''''_\<sigma>''''': "mthr.if.mthr.silent_moves \<sigma>'''' \<sigma>'''''"
          and red_a': "mthr.if.redT \<sigma>''''' (t_a', ta_a') \<sigma>''''''"
          and "\<not> mthr.if.m\<tau>move \<sigma>''''' (t_a', ta_a') \<sigma>''''''"
          and \<tau>Runs''''': "mthr.if.mthr.\<tau>Runs \<sigma>'''''' (tdropn (Suc (a'_m - Suc a_m)) ?E')"
          unfolding E'_a'_m' by cases
        from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
          unfolding in_set_conv_nth by blast
        with red_a' obtain x_a' x'_a' m'_a' 
          where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>''''') ta_a' (x'_a', m'_a')"
          and \<sigma>'''''': "redT_upd \<sigma>''''' t_a' ta_a' x'_a' m'_a' \<sigma>''''''"
          and ts_t_a': "thr \<sigma>''''' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
          by cases auto
        from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
        obtain ta'_a' X_a' X'_a' xs'_a'
          where x_a': "x_a' = (Running, X_a')"
          and x'_a': "x'_a' = (Running, X'_a')"
          and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
          and red''_a': "t_a' \<turnstile> (X_a', shr \<sigma>''''') -ta'_a'\<rightarrow> (X'_a', m'_a')"
          by cases fastsimp+
        from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
          and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
        hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
        with red''_a' have typeof_ad': "typeof_addr (shr \<sigma>''''') ad = None"
          by(auto dest: red_New_typeof_addrD)
    
        have "m'_a = shr \<sigma>'''" using \<sigma>''' by auto
        also have "shr \<sigma>''' \<unlhd> shr \<sigma>''''" using \<sigma>'''_\<sigma>'''' by(rule init_fin_\<tau>rtrancl3p_hext)
        also from \<sigma>''''_\<sigma>''''' have "shr \<sigma>'''' \<unlhd> shr \<sigma>'''''" by(rule init_fin_silent_moves_hext)
        finally have "typeof_addr (shr \<sigma>''''') ad \<noteq> None" using typeof_m'_a_ad by(auto dest: typeof_addr_hext_mono)
        with typeof_ad' show False by contradiction
      qed
      
      from `a_m \<le> a'_m` have [simp]: "a_m = a'_m"
      proof(rule le_antisym)
        show "a'_m \<le> a_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence "a_m < a'_m" by simp
          hence "(\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a_m..<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            by(simp add: setsum_upto_add_nat)
          with a'_less `a_m < a'_m` E'_a_m a_n a'_n show False
            unfolding a'_conv a_conv by(subst (asm) setsum_head_upt_Suc) simp_all
        qed
      qed
      with E'_a_m E'_a'_m have [simp]: "t_a' = t_a" "ta_a' = ta_a" by simp_all
      from New_ta_a' a'_n ta_a have a'_n': "a'_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>"
        and New_ta'_a': "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'" by auto
      with red''_a New_ta'_a a_n' have "a'_n = a_n"
        by(auto dest: red_New_same_addr_same)
      with `a_m = a'_m` have "a - n = a' - n" unfolding a_conv a'_conv by simp
      thus ?thesis using `n \<le> a` `n \<le> a'` by simp
    qed
  qed
qed

lemma redT_\<tau>rtrancl3p_created_objects:
  assumes minimal: "heap_ops_typeof_minimal"
  and red: "mthr.if.mthr.\<tau>rtrancl3p \<sigma> ttas \<sigma>'"
  and type: "typeof_addr (shr \<sigma>') a = \<lfloor>T\<rfloor>" "typeof_addr (shr \<sigma>) a = None"
  shows "\<exists>t ta CTn. (t, ta) \<in> set ttas \<and> NormalAction (NewHeapElem a CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> shr \<sigma>' \<turnstile>a a : CTn"
using red type
proof induct
  case \<tau>rtrancl3p_refl thus ?case by simp
next
  case (\<tau>rtrancl3p_\<tau>step \<sigma> \<sigma>' ttls \<sigma>'' ttl)
  obtain t tl where ttl: "ttl = (t, tl)" by(cases ttl)
  from `mthr.if.redT \<sigma> ttl \<sigma>'` `mthr.if.m\<tau>move \<sigma> ttl \<sigma>'`
  have "shr \<sigma>' = shr \<sigma>" using mthr.if.m\<tau>move_heap[of \<sigma> t tl \<sigma>']
    unfolding ttl by simp
  with ttl \<tau>rtrancl3p_\<tau>step show ?case by simp
next
  case (\<tau>rtrancl3p_step \<sigma> \<sigma>' ttls \<sigma>'' ttl)
  note type_\<sigma>_a = `typeof_addr (shr \<sigma>) a = None`

  show ?case
  proof(cases "typeof_addr (shr \<sigma>') a = None")
    case True
    with \<tau>rtrancl3p_step show ?thesis by fastsimp
  next
    case False
    
    from `mthr.if.mthr.\<tau>rtrancl3p \<sigma>' ttls \<sigma>''`
    have hext: "shr \<sigma>' \<unlhd> shr \<sigma>''" by(rule init_fin_\<tau>rtrancl3p_hext)
    with False `typeof_addr (shr \<sigma>'') a = \<lfloor>T\<rfloor>`
    have type_\<sigma>'_a: "typeof_addr (shr \<sigma>') a = \<lfloor>T\<rfloor>"
      by(auto dest: typeof_addr_hext_mono)

    with `mthr.if.redT \<sigma> ttl \<sigma>'` type_\<sigma>_a
    obtain t ta x x' where ttl: "ttl = (t, ta)"
      and red_if: "t \<turnstile> (x, shr \<sigma>) -ta\<rightarrow>i (x', shr \<sigma>')"
      by cases fastsimp+
    
    from red_if type_\<sigma>_a type_\<sigma>'_a obtain X ta' X'
      where x: "x = (Running, X)" and x': "x' = (Running, X')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red: "t \<turnstile> (X, shr \<sigma>) -ta'\<rightarrow> (X', shr \<sigma>')"
      by cases fastsimp+
    
    from minimal red type_\<sigma>'_a type_\<sigma>_a obtain CTn
      where "NewHeapElem a CTn \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" "ty_of_htype CTn = T" "shr \<sigma>' \<turnstile>a a : CTn"
      by(auto dest: red_created_object simp add: split_beta)
    with hext show ?thesis using ta ttl
      by(fastsimp simp del: split_paired_Ex intro: htypeof_addr_hext_mono)
  qed
qed

lemma JMM_inst_aux: 
  assumes minimal: "heap_ops_typeof_minimal"
  and start_heap: "start_heap_ok"
  and wfix_start: "ts_inv (init_fin_lift_inv wfix) I (thr (start_state f P C M vs)) (shr (start_state f P C M vs))"
  and wfx_start: "ts_ok (init_fin_lift wfx) (thr (start_state f P C M vs)) (shr (start_state f P C M vs))"
  shows "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                         mthr.if.\<E> (start_state f P C M vs))
                        P"
  (is "executions_sc ?E _")
proof -
  let ?start_state = "start_state f P C M vs"
  let ?obs_prefix = "llist_of (lift_start_obs start_tid start_heap_obs)"

  show ?thesis
  proof
    fix E a adal a'
    assume "E \<in> ?E" "a \<in> new_actions_for P E adal" "a' \<in> new_actions_for P E adal"
    thus "a = a'" by(rule \<E>_new_actions_for_unique)
  next
    fix E ra adal
    assume E: "E \<in> ?E"
      and ra: "ra \<in> read_actions E"
      and adal: "adal \<in> action_loc P E ra"

    obtain ad al where ad_al: "adal = (ad, al)" by(cases adal)

    from E obtain E'' where E: "E = lappend ?obs_prefix E''"
      and E'': "E'' \<in> mthr.if.\<E> (start_state f P C M vs)" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and \<tau>Runs: "mthr.if.mthr.\<tau>Runs (start_state f P C M vs) E'"
      by(rule mthr.if.\<E>.cases)

    have ra_len: "length (lift_start_obs start_tid start_heap_obs) \<le> ra"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "ra < length (lift_start_obs start_tid start_heap_obs)" by simp
      moreover with ra E obtain ra' ad al v 
        where "start_heap_obs ! ra' = ReadMem ad al v" "ra' < length start_heap_obs"
        unfolding lift_start_obs_def
        by cases(auto elim!: actionsE simp add: action_obs_def lnth_lappend1 lnth_llist_of lnth_LCons split: nat.split_asm)
      ultimately have "ReadMem ad al v \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
      thus False by(simp add: start_heap_obs_not_Read)
    qed
    let ?n = "length (lift_start_obs start_tid start_heap_obs)"
    from ra ra_len E have ra: "ra - ?n \<in> read_actions E''"
      by cases(auto simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)

    from ra ra_len adal ad_al E obtain v
      where ra_obs: "action_obs E'' (ra - ?n) = NormalAction (ReadMem ad al v)"
      by(auto elim!: read_actions.cases simp add: action_obs_def lnth_lappend2)
      
    from ra have "ra - ?n \<in> actions E''" by(auto)
    hence "Fin (ra - ?n) < llength E''" by(rule actionsE)
    with \<tau>Runs obtain ra_m ra_n t_ra ta_ra 
      where E_ra: "lnth E'' (ra - ?n) = (t_ra, \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub> ! ra_n)"
      and ra_n: "ra_n < length \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>" and ra_m: "Fin ra_m < tlength E'"
      and ra_conv: "ra - ?n = (\<Sum>i<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + ra_n"
      and E'_ra_m: "tnth E' ra_m = (t_ra, ta_ra)"
      unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
    let ?E' = "tdropn (Suc ra_m) E'"
    
    have E'_unfold: "E' = lappendt (ltake (Fin ra_m) (llist_of_tllist E')) (TCons (tnth E' ra_m) ?E')"
      unfolding tdropn_Suc_conv_tdropn[OF ra_m] lappendt_ltake_tdropn ..
    hence "mthr.if.mthr.\<tau>Runs (start_state f P C M vs) (lappendt (ltake (Fin ra_m) (llist_of_tllist E')) (TCons (tnth E' ra_m) ?E'))"
      using \<tau>Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.\<tau>rtrancl3p (start_state f P C M vs) (list_of (ltake (Fin ra_m) (llist_of_tllist E'))) \<sigma>'"
      and \<tau>Runs': "mthr.if.mthr.\<tau>Runs \<sigma>' (TCons (tnth E' ra_m) ?E')"
      by(rule mthr.if.mthr.\<tau>Runs_lappendtE) simp
    from \<tau>Runs' obtain \<sigma>'' \<sigma>''' where \<sigma>'_\<sigma>'': "mthr.if.mthr.silent_moves \<sigma>' \<sigma>''"
      and red_ra: "mthr.if.redT \<sigma>'' (t_ra, ta_ra) \<sigma>'''"
      and "\<not> mthr.if.m\<tau>move \<sigma>'' (t_ra, ta_ra) \<sigma>'''"
      and \<tau>Runs'': "mthr.if.mthr.\<tau>Runs \<sigma>''' ?E'"
      unfolding E'_ra_m by cases

    note \<sigma>_\<sigma>'
    also note mthr.if.mthr.silent_moves_into_\<tau>rtrancl3p[OF \<sigma>'_\<sigma>'']
    finally have \<sigma>_\<sigma>'': "mthr.if.mthr.\<tau>rtrancl3p (start_state f P C M vs) (list_of (ltake (Fin ra_m) (llist_of_tllist E'))) \<sigma>''"
      by simp


    let ?I' = "upd_invs I (init_fin_lift_inv wfix) (concat (map (thr_a \<circ> snd) (list_of (ltake (Fin ra_m) (llist_of_tllist E')))))"
    from \<sigma>_\<sigma>'' wfix_start wfx_start have wfix': "ts_inv (init_fin_lift_inv wfix) ?I' (thr \<sigma>'') (shr \<sigma>'')"
      by(rule wfix_if.redT_\<tau>rtrancl3p_invariant)

    from \<sigma>_\<sigma>'' wfx_start have wfx': "ts_ok (init_fin_lift wfx) (thr \<sigma>'') (shr \<sigma>'')"
      by(rule wfix_if.redT_\<tau>rtrancl3p_preserves)

    from \<sigma>_\<sigma>'' have "shr (start_state f P C M vs) \<unlhd> shr \<sigma>''" by(rule init_fin_\<tau>rtrancl3p_hext)
    hence hext: "start_heap \<unlhd> shr \<sigma>''" unfolding init_fin_lift_state_conv_simps shr_start_state .

    from E_ra ra_n ra_obs have "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>"
      by(auto simp add: action_obs_def in_set_conv_nth)
    with red_ra obtain x_ra x'_ra m'_ra 
      where red'_ra: "mthr.init_fin t_ra (x_ra, shr \<sigma>'') ta_ra (x'_ra, m'_ra)"
      and \<sigma>''': "redT_upd \<sigma>'' t_ra ta_ra x'_ra m'_ra \<sigma>'''"
      and ts_t_a: "thr \<sigma>'' t_ra = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
      by cases auto
    from red'_ra `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>`
    obtain ta'_ra X_ra X'_ra
      where x_ra: "x_ra = (Running, X_ra)"
      and x'_ra: "x'_ra = (Running, X'_ra)"
      and ta_ra: "ta_ra = convert_TA_initial (convert_obs_initial ta'_ra)"
      and red''_ra: "t_ra \<turnstile> (X_ra, shr \<sigma>'') -ta'_ra\<rightarrow> (X'_ra, m'_ra)"
      by cases fastsimp+

    from wfix' ts_t_a obtain I_t
      where wfix_ra: "init_fin_lift_inv wfix I_t t_ra x_ra (shr \<sigma>'')"
      by(auto dest: ts_invD)

    from wfx' ts_t_a have wfx_ra: "init_fin_lift wfx t_ra x_ra (shr \<sigma>'')" by(auto dest: ts_okD)

    from `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>` ta_ra 
    have "ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>" by auto

    with red''_ra wfx_ra wfix_ra x_ra obtain T' where wt_adal: "P,shr \<sigma>'' \<turnstile> ad@al : T'"
      by(auto dest: red_read_typeable)
    
    show "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
    proof(cases "ad \<in> set start_addrs")
      case True
      then obtain CTn where CTn: "NewHeapElem ad CTn \<in> set start_heap_obs"
        by(blast dest: start_addrs_NewHeapElem_start_heap_obsD)
      then obtain wa where wa: "wa < length start_heap_obs" "start_heap_obs ! wa = NewHeapElem ad CTn"
        unfolding in_set_conv_nth by blast
      hence wa_action: "Suc wa \<in> actions E" unfolding E lift_start_obs_def
        by(auto simp add: lnth_lappend1 actions_def Fin_less_Fin_plusI iSuc_Fin[symmetric] intro: ileI1)
      moreover
      from wa E have new_wa: "is_new_action (action_obs E (Suc wa))"
        by(simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
      moreover
      have "(ad, al) \<in> action_loc P E (Suc wa)"
      proof(cases CTn)
        case (Class_type C)
        with CTn have "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>" by(simp add: NewObj_start_heap_obsD)
        with typeof_addr_hext_mono[OF hext this] wt_adal wa ad_al ra_obs ra_len adal Class_type E
        show ?thesis
          by(fastsimp elim!: addr_loc_type.cases simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
      next
        case (Array_type U n)
        with CTn have "typeof_addr start_heap ad = \<lfloor>Array U\<rfloor>" "n = array_length start_heap ad"
          by(simp_all add: NewArr_start_heap_obsD)
        with typeof_addr_hext_mono[OF hext this(1)] hext_arrD[OF hext this(1)]
          wt_adal wa ad_al ra_obs ra_len adal Array_type E
        show ?thesis
          by(auto elim!: addr_loc_type.cases simp add: action_obs_def lnth_lappend1 lnth_lappend2 lift_start_obs_def)
      qed
      ultimately have "Suc wa \<in> new_actions_for P E adal" unfolding ad_al by(simp add: new_actions_for_def)
      moreover have "Suc wa < ra" using wa ra_len by(simp add: lift_start_obs_def)
      ultimately show ?thesis by blast
    next
      case False
      from wt_adal obtain T_ad where T_ad: "typeof_addr (shr \<sigma>'') ad = \<lfloor>T_ad\<rfloor>" by cases

      from False have "typeof_addr start_heap ad = None"
        using dom_typeof_addr_start_heap_eq_start_addrs[OF minimal] by auto
      hence "typeof_addr (shr ?start_state) ad = None" unfolding init_fin_lift_state_conv_simps shr_start_state .
      from redT_\<tau>rtrancl3p_created_objects[OF minimal \<sigma>_\<sigma>'' T_ad this]
      obtain t_wa ta_wa CTn 
        where t_wa_ta_wa: "(t_wa, ta_wa) \<in> set (list_of (ltake (Fin ra_m) (llist_of_tllist E')))"
        and CTn: "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub>"
        and type_wa: "ty_of_htype CTn = T_ad" "shr \<sigma>'' \<turnstile>a ad : CTn" by blast
      from t_wa_ta_wa ra_m obtain wa_m
        where wa_m: "wa_m < ra_m" and E'_wa_m: "tnth E' wa_m = (t_wa, ta_wa)"
        unfolding in_set_conv_nth
        by(auto simp add: lnth_ltake length_list_of_conv_the_Fin min_def split: split_if_asm)
      from wa_m ra_m have wa_m_len: "Fin wa_m < tlength E'"
        by(simp add: less_trans[where y="Fin ra_m"])

      from CTn obtain wa_n where wa_n: "wa_n < length \<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub>"
        and ta_wa_n: "\<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub> ! wa_n = NormalAction (NewHeapElem ad CTn)"
        unfolding in_set_conv_nth by blast
      let ?wa = "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n + length (lift_start_obs start_tid start_heap_obs)"

      have "llength (lconcat (ltake (Fin (Suc wa_m)) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))) =
            (\<Sum>i | i < Suc wa_m \<and> Fin i < tlength E'. (Fin \<circ> (\<lambda>i. length \<lbrace>snd (lnth (ltake (Fin (Suc wa_m)) (llist_of_tllist E')) i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(subst llength_lconcat_lfinite_conv_sum)(simp_all add: split_beta)
      also have "\<dots> = Fin (\<Sum>i | i < Suc wa_m \<and> Fin i < tlength E'. length \<lbrace>snd (lnth (ltake (Fin (Suc wa_m)) (llist_of_tllist E')) i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_inat_def)
      also have "\<dots> = Fin (\<Sum>i<Suc wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        unfolding inat.inject by(rule setsum_cong)(auto intro: le_less_trans[OF _ wa_m_len] simp add: lnth_ltake)
      finally have "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) < 
            llength (lconcat (ltake (Fin (Suc wa_m)) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
                                                           (llist_of_tllist E'))))"
        using wa_n E'_wa_m by simp
      also have "\<dots> \<le> llength E''" unfolding E'
        by(blast intro: lprefix_llength_le lprefix_lconcatI ltake_is_lprefix)
      finally have wa'_len: "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) < llength E''" .
      from lnth_lconcat_conv[OF this[unfolded E']]
      obtain wa_m' wa_n'
        where E''_wa: "lnth E'' ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) = 
                       lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) wa_m') wa_n'"
        and wa_n': "Fin wa_n' < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) wa_m')"
        and wa_m': "Fin wa_m' < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
        and wa': "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) =
                  (\<Sum>i<wa_m'. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin wa_n'"
        unfolding E' by blast

      from wa_m' have wa_m': "Fin wa_m' < tlength E'" by simp
      with wa_n' have wa_n': "wa_n' < length \<lbrace>snd (tnth E' wa_m')\<rbrace>\<^bsub>o\<^esub>" by(simp add: split_beta)
      have "(\<Sum>i<wa_m'. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) =
            (\<Sum>i<wa_m'. (Fin \<circ> (\<lambda>i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(rule setsum_cong)(simp_all add: less_trans[where y="Fin wa_m'"] split_beta wa_m')
      also have "\<dots> = Fin (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_inat_def)
      finally have wa': "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n = (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n'"
        using wa' by simp
      moreover have [simp]: "wa_m' = wa_m"
      proof(rule ccontr)
        assume "wa_m' \<noteq> wa_m"
        thus False unfolding neq_iff
        proof
          assume "wa_m' < wa_m"
          hence "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with wa' have "(\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n = wa_n'" by simp
          moreover have "(\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' wa_m')\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `wa_m' < wa_m`]) simp
          ultimately show False using wa_n' by simp
        next
          assume "wa_m < wa_m'"
          hence "(\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with wa' have "(\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n' = wa_n" by simp
          moreover have "(\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' wa_m)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `wa_m < wa_m'`]) simp
          ultimately show False using wa_n E'_wa_m by simp
        qed
      qed
      ultimately have [simp]: "wa_n' = wa_n" by simp
      from E''_wa wa_m_len wa_n E'_wa_m ta_wa_n
      have "lnth E'' ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) = (t_wa, NormalAction (NewHeapElem ad CTn))"
        by(simp add: split_beta lnth_llist_of)
      hence "action_obs E ?wa = NormalAction (NewHeapElem ad CTn)" unfolding E
        by(simp add: action_obs_def lnth_lappend2)
      moreover hence "adal \<in> action_loc P E ?wa" using ad_al adal type_wa wt_adal
        by(cases CTn)(fastsimp elim!: addr_loc_type.cases)+
      moreover from wa'_len have "?wa \<in> actions E" 
        unfolding actions_def E by(cases "llength E''")(auto)
      ultimately have "?wa \<in> new_actions_for P E adal" by(simp add: new_actions_for_def)
      moreover
      {
        have "(\<Sum>i<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) =
              (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m..<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          using wa_m unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
        also have "\<dots> > (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n"
          using wa_n E'_wa_m by(subst setsum_head_upt_Suc[OF wa_m]) simp
        finally have "ra - length (lift_start_obs start_tid start_heap_obs) > (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n"
          unfolding ra_conv by simp
        hence "?wa < ra" using ra_len by simp }
      ultimately show ?thesis by blast
    qed
  qed
qed

end

locale heap_jmm =
  heap_conf_read empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write hconf P +
  heap_jmm_aux empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write final r \<tau>move wfx wfix P
  for empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and hconf :: "'heap \<Rightarrow> bool"
  and final :: "'x \<Rightarrow> bool"
  and r :: "(addr, thread_id, 'x, 'heap, addr, obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and \<tau>move :: "(addr, thread_id, 'x, 'heap, addr, obs_event) \<tau>moves" 
  and wfx :: "thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and wfix :: "'i \<Rightarrow> thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'md prog"
  +
  assumes red_NewArr_lengthD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length m' a = n"
  and red_write_typeable:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; wfix I t x m; WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,m' \<turnstile> ad@al : T' \<and> P,m' \<turnstile> v :\<le> T'"
begin

lemma red_mrw_values_typeable:
  assumes vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,m \<turnstile> ad@al : T \<and> P,m \<turnstile> v :\<le> T"
  and red: "t \<turnstile> (x, m) -ta\<rightarrow> (x', m')"
  and wfx: "wfx t x m"
  and wfix: "wfix I t x m"
  and vs': "mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,m' \<turnstile> ad@al : T \<and> P,m' \<turnstile> v :\<le> T"
proof(cases "vs (ad, al) = \<lfloor>(v, b)\<rfloor>")
  case True
  hence "\<exists>T. P,m \<turnstile> ad@al : T \<and> P,m \<turnstile> v :\<le> T" by(rule vs)
  moreover from red have "m \<unlhd> m'" by(rule red_hext_incr)
  ultimately show ?thesis by(auto intro: conf_hext addr_loc_type_hext_mono)
next
  case False
  with mrw_values_eq_SomeD[OF vs']
  obtain obs' wa obs'' 
    where eq: "map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  show ?thesis
  proof(cases "is_new_action wa")
    case False with `is_write_action wa`
    obtain ad' al' v' where "wa = NormalAction (WriteMem ad' al' v')"
      by cases auto
    with vwa adal eq have "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
      by(auto simp add: map_eq_append_conv)
    with red wfx wfix show ?thesis by(auto dest!: red_write_typeable)
  next
    case True
    then obtain ad' CTn where wa: "wa = NormalAction (NewHeapElem ad' CTn)"
      by cases auto
    with vwa adal eq have new: "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and [simp]: "ad' = ad"
      by(auto simp add: map_eq_append_conv)
    from red_New_typeof_addrD[OF red this(1)]
    have "typeof_addr m' ad = \<lfloor>ty_of_htype CTn\<rfloor>" by simp
    moreover {
      fix T n
      assume "CTn = Array_type T n"
      with new have "NewArr ad T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
      from red_NewArr_lengthD[OF red this]
      have "array_length m' ad = n" by(simp) }
    ultimately show ?thesis using adal wa vwa
      by(fastsimp simp add: has_field_def intro: addr_loc_type.intros)
  qed
qed

lemma if_red_mrw_values_typeable:
  assumes vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,m \<turnstile> ad@al : T \<and> P,m \<turnstile> v :\<le> T"
  and red: "mthr.init_fin t ((s, x), m) ta ((s', x'), m')"
  and wt: "wfx t x m" "wfix I t x m"
  and vs': "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,m' \<turnstile> ad@al : T \<and> P,m' \<turnstile> v :\<le> T"
using red vs' vs
by cases(auto intro: red_mrw_values_typeable[OF vs _ wt])

lemma redT_mrw_values_typeable:
  assumes vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T"
  and red: "mthr.if.redT s (t,ta) s'"
  and wfx: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and wfix: "ts_inv (init_fin_lift_inv wfix) I (thr s) (shr s)"
  and vs': "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T"
using red
proof(cases)
  case (redT_normal x x' m')
  then obtain \<sigma> X \<sigma>' X'
    where x: "x = (\<sigma>, X)" "x' = (\<sigma>', X')"
    and red: "t \<turnstile> ((\<sigma>, X), shr s) -ta\<rightarrow>i ((\<sigma>', X'), m')"
    and m': "m' = shr s'"
    and tst: "thr s t = \<lfloor>((\<sigma>, X), no_wait_locks)\<rfloor>"
    by(cases x)(cases x', fastsimp)
  from wfx wfix tst obtain I where "wfx t X (shr s)" "wfix I t X (shr s)"
    by(auto dest!: ts_invD ts_okD)
  with vs red show ?thesis using vs' unfolding m' by(rule if_red_mrw_values_typeable)
next
  case (redT_acquire x ln n)
  have "mrw_values P vs (map NormalAction (convert_RA ln)) (ad, al) = vs (ad, al)"
    by(rule mrw_values_no_write_unchanged)(auto dest: convert_RA_not_write)
  with redT_acquire vs' show ?thesis by(auto intro: vs)
qed

lemma \<tau>RedT_mrw_values_typeable:
  assumes vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T"
  and red: "mthr.if.mthr.\<tau>rtrancl3p s ttas s'"
  and wfx: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and wfix: "ts_inv (init_fin_lift_inv wfix) I (thr s) (shr s)"
  and vs': "mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    (is "mrw_values _ _ (?conv ttas) _ = _")
  shows "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T"
using red wfx wfix vs vs'
proof(induct arbitrary: vs I)
  case (\<tau>rtrancl3p_refl s) thus ?case by simp
next
  case (\<tau>rtrancl3p_step s s' tls s'' tl)
  from `mthr.if.redT s tl s'` obtain t ta
    where tl: "tl = (t, ta)"
    and red: "mthr.if.redT s (t, ta) s'"
    by(cases tl) fastsimp
  
  note vs = `vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T`
  note wfix = `ts_inv (init_fin_lift_inv wfix) I (thr s) (shr s)`
  note wfx = `ts_ok (init_fin_lift wfx) (thr s) (shr s)`
  with red have thread_ok': "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
    by(rule wfix_if.if.redT_preserves)
  moreover from red wfix wfx
  obtain I' where "ts_inv (init_fin_lift_inv wfix) I' (thr s') (shr s')"
    by(blast dest: wfix_if.if.redT_invariant)
  moreover {
    assume "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
    with vs red wfx wfix have "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T"
      by(rule redT_mrw_values_typeable) }
  moreover from `mrw_values P vs (?conv (tl # tls)) (ad, al) = \<lfloor>(v, b)\<rfloor>`
  have "mrw_values P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    unfolding tl by simp
  ultimately show ?case by(rule \<tau>rtrancl3p_step.hyps)
next
  case (\<tau>rtrancl3p_\<tau>step s s' tls s'' tl vs)
  from `mthr.if.redT s tl s'` obtain t ta
    where tl: "tl = (t, ta)"
    and red: "mthr.if.redT s (t, ta) s'"
    by(cases tl) fastsimp
  
  note vs = `vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T`
  note wfix = `ts_inv (init_fin_lift_inv wfix) I (thr s) (shr s)`
  note wfx = `ts_ok (init_fin_lift wfx) (thr s) (shr s)`
  with red have wfx': "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
    by(rule wfix_if.if.redT_preserves)
  moreover from red wfix wfx
  obtain I' where "ts_inv (init_fin_lift_inv wfix) I' (thr s') (shr s')"
    by(blast dest: wfix_if.if.redT_invariant)
  moreover {
    assume "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
    with vs red wfx wfix
    have "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T" 
      by(rule redT_mrw_values_typeable) }
  moreover from `mthr.if.m\<tau>move s tl s'`
  have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []" unfolding tl
    by(auto elim!: mthr.if.m\<tau>move.cases dest: mthr.if.silent_tl)
  with `mrw_values P vs (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>`
  have "mrw_values P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>" by simp
  ultimately show ?case by(rule \<tau>rtrancl3p_\<tau>step.hyps)
qed

end

end
