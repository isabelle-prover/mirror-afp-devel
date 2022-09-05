(* Title: thys/Abacus_Hoare.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
   Modifications: Franz Regensburger (FABR) 04/2022
      added comments and lemmas for clarification
 *)

section \<open>Hoare Rules for Abacus Programs\<close>

theory Abacus_Hoare
  imports Abacus
begin

type_synonym abc_assert = "nat list \<Rightarrow> bool"

definition 
  assert_imp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" ("_ \<mapsto> _" [0, 0] 100)
  where
    "assert_imp P Q \<equiv> \<forall>xs. P xs \<longrightarrow> Q xs"

fun abc_holds_for :: "(nat list \<Rightarrow> bool) \<Rightarrow> (nat \<times> nat list) \<Rightarrow> bool" ("_ abc'_holds'_for _" [100, 99] 100)
  where
    "P abc_holds_for (s, lm) = P lm"  

(* Hoare Rules *)
(* halting case *)
(*consts abc_Hoare_halt :: "abc_assert \<Rightarrow> abc_prog \<Rightarrow> abc_assert \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)*)

fun abc_final :: "(nat \<times> nat list) \<Rightarrow> abc_prog \<Rightarrow> bool"
  where 
    "abc_final (s, lm) p = (s = length p)"

fun abc_notfinal :: "abc_conf \<Rightarrow> abc_prog \<Rightarrow> bool"
  where
    "abc_notfinal (s, lm) p = (s < length p)"

(* SPIKE: added by FABR:

  The definitions for abc_final and abc_notfinal are somewhat surprising.
  It is easy to build an abacus program p that jumps to a state length p < s

  Thus, there are programs, that may reach a configuration that is neither abc_final nor abc_notfinal.

  We add a definition abc_out_of_prog and provide a witness for our conjecture.

 *)

fun abc_out_of_prog :: "abc_conf \<Rightarrow> abc_prog \<Rightarrow> bool"
  where
    "abc_out_of_prog (s, lm) p = (length p < s)"

definition abcP_out_of_pgm_ex :: abc_prog
  where
   "abcP_out_of_pgm_ex = [Dec 0 41, Inc 1, Goto 0]"

(* ABC program abcP_out_of_pgm_ex can reach state 41, which is out of program *)

lemma "abc_steps_l (0,[5,3]) abcP_out_of_pgm_ex (10 +6) = (41, [0, 8])"
  by (simp add: abc_steps_l.simps abc_step_l.simps abc_fetch.simps abc_lm_v.simps abc_lm_s.simps
                numeral_eqs_upto_12
                abcP_out_of_pgm_ex_def )

lemma "abc_out_of_prog (abc_steps_l (0,[5,3]) abcP_out_of_pgm_ex (10 +6)) abcP_out_of_pgm_ex"
  by (simp add: abc_steps_l.simps abc_step_l.simps abc_fetch.simps  abc_lm_v.simps abc_lm_s.simps
                numeral_eqs_upto_12
                abcP_out_of_pgm_ex_def )

(* From the properties abc_notfinal cf p, abc_final cf p, abc_out_of_prog cf holds
 *   always one of these exlusively holds (the other two are ruled out)
 *)

lemma "abc_notfinal cf p \<or> abc_final cf p \<or> abc_out_of_prog cf p"
  by (metis (full_types) abc_final.elims(3) abc_notfinal.elims(3) abc_out_of_prog.elims(3)  not_less_iff_gr_or_eq prod.sel(1))

lemma "\<lbrakk> length p \<noteq> 0; abc_notfinal cf p \<rbrakk> \<Longrightarrow> \<not> abc_final cf p \<and> \<not> abc_out_of_prog cf p"
  by (metis abc_final.simps abc_notfinal.elims(2) abc_out_of_prog.simps less_Suc_eq nat_neq_iff not_less_eq)

lemma "\<lbrakk> length p \<noteq> 0; abc_final cf p \<rbrakk> \<Longrightarrow> \<not> abc_notfinal cf p \<and> \<not> abc_out_of_prog cf p"
  by (metis abc_final.elims(2) abc_final.simps abc_notfinal.elims(2) abc_out_of_prog.simps nat_neq_iff)

lemma "\<lbrakk> length p \<noteq> 0; abc_out_of_prog cf p \<rbrakk> \<Longrightarrow> \<not> abc_notfinal cf p \<and> \<not> abc_final cf p"
  by (metis abc_final.simps abc_notfinal.simps abc_out_of_prog.simps less_iff_Suc_add less_imp_add_positive less_not_refl not_less_eq old.prod.exhaust)

(* END SPIKE: added by FABR *)

definition 
  abc_Hoare_halt :: "abc_assert \<Rightarrow> abc_prog \<Rightarrow> abc_assert \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
    "abc_Hoare_halt P p Q \<equiv> \<forall>lm. P lm \<longrightarrow> (\<exists>n. abc_final (abc_steps_l (0, lm) p n) p \<and> Q abc_holds_for (abc_steps_l (0, lm) p n))"

lemma abc_Hoare_haltI:
  assumes "\<And>lm. P lm \<Longrightarrow> \<exists>n. abc_final (abc_steps_l (0, lm) p n) p \<and> Q abc_holds_for (abc_steps_l (0, lm) p n)"
  shows " \<lbrace>P\<rbrace> (p::abc_prog) \<lbrace>Q\<rbrace> "
  unfolding abc_Hoare_halt_def 
  using assms by auto

(*
  \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>   \<lbrace>Q\<rbrace> B \<lbrace>S\<rbrace> 
  -----------------------------------------
  \<lbrace>P\<rbrace> A [+] B \<lbrace>S\<rbrace>
*)

(* Added by FABR for clarification and presentation in classes *)

fun app_mopup :: "tprog0 \<Rightarrow> nat \<Rightarrow> tprog0"
  where
    "app_mopup tp n = tp @ shift (mopup_n_tm n) (length tp div 2)"

lemma compile_correct_halt_2:
  assumes compile: "tp = tm_of ap"
    and abc_halt: "abc_steps_l (0, ns) ap stp = (length ap, am)"
    and rs_loc: "n < length am"
  shows "\<exists>stp i j. steps0 (Suc 0, [Bk,Bk], <ns::nat list>) (app_mopup tp n) stp = (0, Bk\<up>i, <abc_lm_v am n> @ Bk\<up>j)"
proof -
  have crsp: "crsp (layout_of ap) (0, ns) (Suc 0, [Bk,Bk], <ns::nat list>) []"
    by (auto simp add: start_of.simps crsp.simps)
  with assms have "\<exists> stp i j. steps (Suc 0, [Bk,Bk], <ns::nat list>) (tp @ shift (mopup_n_tm n) (length tp div 2), 0) stp
                     = (0, Bk\<up>i @ Bk # Bk # [], Oc\<up>Suc (abc_lm_v am n) @ Bk\<up>j)"
    using compile_correct_halt by simp
  then have "\<exists>stp i j. steps (Suc 0, [Bk,Bk], <ns::nat list>) (tp @ shift (mopup_n_tm n) (length tp div 2), 0) stp
                     = (0, Bk\<up>i, Oc\<up>Suc (abc_lm_v am n) @ Bk\<up>j)"
    by (metis replicate_app_Cons_same replicate_append_same take_suc)
  then show ?thesis
    by (simp add: tape_of_nat_def)
qed

lemma compile_correct_halt_3:
  assumes compile: "tp = tm_of ap"
    and abc_halt: "abc_steps_l (0, ns) ap stp = (length ap, am)"
    and rs_loc: "n < length am"
  shows "\<exists>stp i j. steps0 (Suc 0, [], <ns::nat list>) (app_mopup tp n) stp = (0, Bk\<up>i, <abc_lm_v am n> @ Bk\<up>j)"
  using steps_left_tape_ShrinkBkCtx_to_NIL compile_correct_halt_2
  by (metis abc_halt compile replicate_Suc replicate_once rs_loc take_suc)

lemma compile_correct_halt_4:
  assumes compile: "tp = tm_of ap"
    and abc_halt: "abc_steps_l (0, ns) ap stp = (length ap, am)"
    and rs_loc: "n < length am"
  shows "TMC_yields_num_res (app_mopup tp n) ns (abc_lm_v am n)"
  unfolding TMC_yields_num_res_def
  using compile_correct_halt_3 
  by (metis One_nat_def abc_halt compile rs_loc)

(* Abacus program ap executed with initial memory ns yields result n in register r *)

definition ABC_yields_res :: "abc_prog \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "ABC_yields_res ap ns n r \<equiv>
           (\<exists>stp am.  abc_steps_l (0, ns) ap stp = (length ap, am) \<and>
                       r < length am \<and> (abc_lm_v am r = n))"

definition ABC_loops_on :: "abc_prog \<Rightarrow> nat list \<Rightarrow>  bool"
  where "ABC_loops_on ap ns \<equiv>
          \<forall>stp. abc_notfinal (abc_steps_l (0, ns) ap stp) ap"

theorem ABC_yields_res_imp_TMC_yields_num_res:
  assumes "tp = tm_of ap"
    and   "ABC_yields_res ap ns n r"
  shows   "TMC_yields_num_res (app_mopup tp r) ns n"
proof -
  from \<open>ABC_yields_res ap ns n r\<close>
  have "\<exists>stp am. abc_steps_l (0, ns) ap stp = (length ap, am) \<and>
                 r < length am \<and> (abc_lm_v am r = n)"
    unfolding ABC_yields_res_def
    by auto
  then obtain stp am where
    w_stp_am: "abc_steps_l (0, ns) ap stp = (length ap, am) \<and>
               r < length am \<and> (abc_lm_v am r = n)" by blast
  have "TMC_yields_num_res (app_mopup tp r) ns (abc_lm_v am r)"
  proof (rule compile_correct_halt_4)
    from assms show "tp = tm_of ap" by auto
  next
    from w_stp_am
    show "r < length am"
      by auto
  next
    from w_stp_am
    show "abc_steps_l (0, ns) ap stp = (length ap, am)"
      by auto
  qed
  with w_stp_am  show "TMC_yields_num_res (app_mopup tp r) ns n" by auto
qed

lemma abc_unhalt_2:
  assumes compile: "tp = tm_of ap"
  and notfinal: "\<forall>stp. abc_notfinal (abc_steps_l (0, ns) ap stp) ap"
shows "\<forall>stp.\<not> is_final (steps0 (Suc 0, [Bk,Bk], <ns::nat list>) (app_mopup tp r) stp)"
proof -
  have "\<forall>stp.\<not> is_final (steps (1, [Bk,Bk], <ns::nat list>) (tp @ shift (mopup_n_tm r) (length tp div 2), 0) stp)"
  proof (rule  compile_correct_unhalt)
    show "layout_of ap = layout_of ap" by auto
  next
    from compile show "tp = tm_of ap" by auto
  next
    show "length tp div 2 = length tp div 2" by auto
  next
    show "crsp (layout_of ap) (0, ns) (1, [Bk, Bk], <ns::nat list>) []"
      by (auto simp add: start_of.simps crsp.simps)
  next
    from notfinal show " \<forall>stp. case abc_steps_l (0, ns) ap stp of (as, am) \<Rightarrow> as < length ap"
      by (metis abc_notfinal.elims(2) case_prodI2 prod.sel(1))
  qed
  then show ?thesis by auto
qed

theorem ABC_loops_imp_TMC_loops:
  assumes "tp = tm_of ap"
    and   "ABC_loops_on ap ns"
  shows   "TMC_loops (app_mopup tp r) ns"
proof -
  have "\<forall>stp.\<not> is_final (steps0 (Suc 0, [Bk,Bk], <ns::nat list>) (app_mopup tp r) stp)"
  proof (rule abc_unhalt_2)
    from \<open>tp = tm_of ap\<close> 
    show "tp = tm_of ap" by auto
  next
    from \<open>ABC_loops_on ap ns\<close>
    show "\<forall>stp. abc_notfinal (abc_steps_l (0, ns) ap stp) ap"
      unfolding ABC_loops_on_def by auto
  qed
  have "\<forall>stp. \<not> is_final (steps0 (Suc 0, [], <ns>) (app_mopup tp r) stp)"
  proof
    fix stp
    show "\<not> is_final (steps0 (Suc 0, [], <ns>) (app_mopup tp r) stp)"
    proof
      assume "is_final (steps0 (Suc 0, [], <ns>) (app_mopup tp r) stp)"
      then have "\<exists>ltap rtap. steps0 (Suc 0, Bk \<up>0, <ns>) (app_mopup tp r) stp = (0, ltap, rtap)"
        using is_final.elims(2) replicate_empty by fastforce
      then obtain ltap rtap where
        "steps0 (Suc 0, Bk \<up>0, <ns>) (app_mopup tp r) stp = (0, ltap, rtap)" by blast
      then have   "\<exists>z3. z3 \<le> 0 + 2 \<and>
        steps0 (Suc 0, Bk\<up>(0 + 2), <ns>)  (app_mopup tp r) stp = (0,ltap @ Bk\<up>z3 ,rtap)"
        using steps_left_tape_EnlargeBkCtx_arbitrary_CL
        by (metis add.left_neutral add_2_eq_Suc' append_Nil)
      then have "is_final (steps0 (Suc 0, [Bk,Bk], <ns>) (app_mopup tp r) stp)"        
        using One_nat_def add_2_eq_Suc' add_Suc_shift is_finalI length_replicate list.size(3)
          list.size(4) plus_1_eq_Suc replicate_Suc replicate_once by force
      with \<open>\<forall>stp. \<not> is_final (steps0 (Suc 0, [Bk, Bk], <ns>) (app_mopup tp r) stp)\<close>
      show False by auto
    qed
  qed
  then show "TMC_loops (app_mopup tp r) ns"
    unfolding TMC_loops_def
    by simp
qed

(* END Added by FABR for clarification and presentation in classes *)

definition
  abc_Hoare_unhalt :: "abc_assert \<Rightarrow> abc_prog \<Rightarrow> bool" ("(\<lbrace>(1_)\<rbrace>/ (_)) \<up>" 50)
  where
    "abc_Hoare_unhalt P p \<equiv> \<forall>args. P args \<longrightarrow> (\<forall>n. abc_notfinal (abc_steps_l (0, args) p n) p)"

lemma abc_Hoare_unhaltI:
  assumes "\<And>args n. P args \<Longrightarrow> abc_notfinal (abc_steps_l (0, args) p n) p"
  shows "\<lbrace>P\<rbrace> (p::abc_prog) \<up>"
  unfolding abc_Hoare_unhalt_def 
  using assms by auto

fun abc_inst_shift :: "abc_inst \<Rightarrow> nat \<Rightarrow> abc_inst"
  where
    "abc_inst_shift (Inc m) n = Inc m" |
    "abc_inst_shift (Dec m e) n = Dec m (e + n)" |
    "abc_inst_shift (Goto m) n = Goto (m + n)"

fun abc_shift :: "abc_inst list \<Rightarrow> nat \<Rightarrow> abc_inst list" 
  where
    "abc_shift xs n = map (\<lambda> x. abc_inst_shift x n) xs" 

fun abc_comp :: "abc_inst list \<Rightarrow> abc_inst list \<Rightarrow> 
                           abc_inst list" (infixl "[+]" 99)
  where
    "abc_comp al bl = (let al_len = length al in 
                           al @ abc_shift bl al_len)"

lemma abc_comp_first_step_eq_pre: 
  "s < length A
 \<Longrightarrow> abc_step_l (s, lm) (abc_fetch s (A [+] B)) = 
    abc_step_l (s, lm) (abc_fetch s A)"
  by(simp add: abc_step_l.simps abc_fetch.simps nth_append)

lemma abc_before_final: 
  "\<lbrakk>abc_final (abc_steps_l (0, lm) p n) p; p \<noteq> []\<rbrakk>
  \<Longrightarrow> \<exists> n'. abc_notfinal (abc_steps_l (0, lm) p n') p \<and> 
            abc_final (abc_steps_l (0, lm) p (Suc n')) p"
proof(induct n)
  case 0
  thus "?thesis"
    by(simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: " \<lbrakk>abc_final (abc_steps_l (0, lm) p n) p; p \<noteq> []\<rbrakk> \<Longrightarrow> 
    \<exists>n'. abc_notfinal (abc_steps_l (0, lm) p n') p \<and> abc_final (abc_steps_l (0, lm) p (Suc n')) p"
    by fact
  have final: "abc_final (abc_steps_l (0, lm) p (Suc n)) p" by fact
  have notnull: "p \<noteq> []" by fact
  show "?thesis"
  proof(cases "abc_final (abc_steps_l (0, lm) p n) p")
    case True
    have "abc_final (abc_steps_l (0, lm) p n) p" by fact
    then have "\<exists>n'. abc_notfinal (abc_steps_l (0, lm) p n') p \<and> abc_final (abc_steps_l (0, lm) p (Suc n')) p"
      using ind notnull
      by simp
    thus "?thesis"
      by simp
  next
    case False
    have "\<not> abc_final (abc_steps_l (0, lm) p n) p" by fact
    from final this have "abc_notfinal (abc_steps_l (0, lm) p n) p" 
      by(case_tac "abc_steps_l (0, lm) p n", simp add: abc_step_red2 
          abc_step_l.simps abc_fetch.simps split: if_splits)
    thus "?thesis"
      using final
      by(rule_tac x = n in exI, simp)
  qed
qed

lemma notfinal_Suc:
  "abc_notfinal (abc_steps_l (0, lm) A (Suc n)) A \<Longrightarrow>  
  abc_notfinal (abc_steps_l (0, lm) A n) A"
  apply(case_tac "abc_steps_l (0, lm) A n")
  apply(simp add: abc_step_red2 abc_fetch.simps abc_step_l.simps split: if_splits)
  done

lemma abc_comp_first_steps_eq_pre: 
  assumes notfinal: "abc_notfinal (abc_steps_l (0, lm)  A n) A"
    and notnull: "A \<noteq> []"
  shows "abc_steps_l (0, lm) (A [+] B) n = abc_steps_l (0, lm) A n"
  using notfinal
proof(induct n)
  case 0
  thus "?case"
    by(simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: "abc_notfinal (abc_steps_l (0, lm) A n) A \<Longrightarrow> abc_steps_l (0, lm) (A [+] B) n = abc_steps_l (0, lm) A n"
    by fact
  have h: "abc_notfinal (abc_steps_l (0, lm) A (Suc n)) A" by fact
  then have a: "abc_notfinal (abc_steps_l (0, lm) A n) A"
    by(simp add: notfinal_Suc)
  then have b: "abc_steps_l (0, lm) (A [+] B) n = abc_steps_l (0, lm) A n"
    using ind by simp
  obtain s lm' where c: "abc_steps_l (0, lm) A n = (s, lm')"
    by (metis prod.exhaust)
  then have d: "s < length A \<and> abc_steps_l (0, lm) (A [+] B) n = (s, lm')" 
    using a b by simp
  thus "?case"
    using c
    by(simp add: abc_step_red2 abc_fetch.simps abc_step_l.simps nth_append)
qed

declare abc_shift.simps[simp del] abc_comp.simps[simp del]
lemma halt_steps2: "st \<ge> length A \<Longrightarrow> abc_steps_l (st, lm) A stp = (st, lm)"
  apply(induct stp)
  by(simp_all add: abc_step_red2 abc_steps_l.simps abc_step_l.simps abc_fetch.simps)

lemma halt_steps: "abc_steps_l (length A, lm) A n = (length A, lm)"
  apply(induct n, simp add: abc_steps_l.simps)
  apply(simp add: abc_step_red2 abc_step_l.simps nth_append abc_fetch.simps)
  done

lemma abc_steps_add: 
  "abc_steps_l (as, lm) ap (m + n) = 
         abc_steps_l (abc_steps_l (as, lm) ap m) ap n"
  apply(induct m arbitrary: n as lm, simp add: abc_steps_l.simps)
proof -
  fix m n as lm
  assume ind: 
    "\<And>n as lm. abc_steps_l (as, lm) ap (m + n) = 
                   abc_steps_l (abc_steps_l (as, lm) ap m) ap n"
  show "abc_steps_l (as, lm) ap (Suc m + n) = 
             abc_steps_l (abc_steps_l (as, lm) ap (Suc m)) ap n"
    apply(insert ind[of as lm "Suc n"], simp)
    apply(insert ind[of as lm "Suc 0"], simp add: abc_steps_l.simps)
    apply(case_tac "(abc_steps_l (as, lm) ap m)", simp)
    apply(simp add: abc_steps_l.simps)
    apply(case_tac "abc_step_l (a, b) (abc_fetch a ap)", 
        simp add: abc_steps_l.simps)
    done
qed

lemma equal_when_halt: 
  assumes exc1: "abc_steps_l (s, lm) A na = (length A, lma)"
    and exc2: "abc_steps_l (s, lm) A nb = (length A, lmb)"
  shows "lma = lmb"
proof(cases "na > nb")
  case True
  then obtain d where "na = nb + d"
    by (metis add_Suc_right less_iff_Suc_add)
  thus "?thesis" using assms halt_steps
    by(simp add: abc_steps_add)
next
  case False
  then obtain d where "nb = na + d"
    by (metis add.comm_neutral less_imp_add_positive nat_neq_iff)
  thus "?thesis" using assms halt_steps
    by(simp add: abc_steps_add)
qed 

lemma abc_comp_first_steps_halt_eq': 
  assumes final: "abc_steps_l (0, lm) A n = (length A, lm')"
    and notnull: "A \<noteq> []"
  shows "\<exists> n'. abc_steps_l (0, lm) (A [+] B) n' = (length A, lm')"
proof -
  have "\<exists> n'. abc_notfinal (abc_steps_l (0, lm) A n') A \<and> 
    abc_final (abc_steps_l (0, lm) A (Suc n')) A"
    using assms
    by(rule_tac n = n in abc_before_final, simp_all)
  then obtain na where a:
    "abc_notfinal (abc_steps_l (0, lm) A na) A \<and> 
            abc_final (abc_steps_l (0, lm) A (Suc na)) A" ..
  obtain sa lma where b: "abc_steps_l (0, lm) A na = (sa, lma)"
    by (metis prod.exhaust)
  then have c: "abc_steps_l (0, lm) (A [+] B) na = (sa, lma)"
    using a abc_comp_first_steps_eq_pre[of lm A na B] assms 
    by simp
  have d: "sa < length A" using b a by simp
  then have e: "abc_step_l (sa, lma) (abc_fetch sa (A [+] B)) = 
    abc_step_l (sa, lma) (abc_fetch sa A)"
    by(rule_tac abc_comp_first_step_eq_pre)
  from a have "abc_steps_l (0, lm) A (Suc na) = (length A, lm')"
    using final equal_when_halt
    by(case_tac "abc_steps_l (0, lm) A (Suc na)" , simp)
  then have "abc_steps_l (0, lm) (A [+] B) (Suc na) = (length A, lm')"
    using a b c e
    by(simp add: abc_step_red2)
  thus "?thesis"
    by blast
qed

lemma abc_exec_null: "abc_steps_l sam [] n = sam"
  apply(cases sam)
  apply(induct n)
   apply(auto simp: abc_step_red2)
   apply(auto simp: abc_step_l.simps abc_steps_l.simps abc_fetch.simps)
  done

lemma abc_comp_first_steps_halt_eq: 
  assumes final: "abc_steps_l (0, lm) A n = (length A, lm')"
  shows "\<exists> n'. abc_steps_l (0, lm) (A [+] B) n' = (length A, lm')"
  using final
  apply(case_tac "A = []")
   apply(rule_tac x = 0 in exI, simp add: abc_steps_l.simps abc_exec_null)
  apply(rule_tac abc_comp_first_steps_halt_eq', simp_all)
  done


lemma abc_comp_second_step_eq: 
  assumes exec: "abc_step_l (s, lm) (abc_fetch s B) = (sa, lma)"
  shows "abc_step_l (s + length A, lm) (abc_fetch (s + length A) (A [+] B))
         = (sa + length A, lma)"
  using assms
  apply(auto simp: abc_step_l.simps abc_fetch.simps nth_append abc_comp.simps abc_shift.simps split : if_splits )
  apply(case_tac [!] "B ! s", auto simp: Let_def)
  done

lemma abc_comp_second_steps_eq:
  assumes exec: "abc_steps_l (0, lm) B n = (sa, lm')"
  shows "abc_steps_l (length A, lm) (A [+] B) n = (sa + length A, lm')"
  using assms
proof(induct n arbitrary: sa lm')
  case 0
  thus "?case"
    by(simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: "\<And>sa lm'. abc_steps_l (0, lm) B n = (sa, lm') \<Longrightarrow> 
    abc_steps_l (length A, lm) (A [+] B) n = (sa + length A, lm')" by fact
  have exec: "abc_steps_l (0, lm) B (Suc n) = (sa, lm')" by fact
  obtain sb lmb where a: " abc_steps_l (0, lm) B n = (sb, lmb)"
    by (metis prod.exhaust)
  then have "abc_steps_l (length A, lm) (A [+] B) n = (sb + length A, lmb)"
    using ind by simp
  moreover have "abc_step_l (sb + length A, lmb) (abc_fetch (sb + length A) (A [+] B)) = (sa + length A, lm') "
    using a exec abc_comp_second_step_eq
    by(simp add: abc_step_red2)    
  ultimately show "?case"
    by(simp add: abc_step_red2)
qed

lemma length_abc_comp[simp, intro]: 
  "length (A [+] B) = length A + length B"
  by(auto simp: abc_comp.simps abc_shift.simps)   

lemma abc_Hoare_plus_halt : 
  assumes A_halt : "\<lbrace>P\<rbrace> (A::abc_prog) \<lbrace>Q\<rbrace>"
    and B_halt : "\<lbrace>Q\<rbrace> (B::abc_prog) \<lbrace>S\<rbrace>"
  shows "\<lbrace>P\<rbrace> (A [+] B) \<lbrace>S\<rbrace>"
proof(rule_tac abc_Hoare_haltI)
  fix lm
  assume a: "P lm"
  then obtain na lma where 
    "abc_final (abc_steps_l (0, lm) A na) A"
    and b: "abc_steps_l (0, lm) A na = (length A, lma)"
    and c: "Q abc_holds_for (length A, lma)"
    using A_halt unfolding abc_Hoare_halt_def
    by (metis (full_types) abc_final.simps abc_holds_for.simps prod.exhaust)
  have "\<exists> n. abc_steps_l (0, lm) (A [+] B) n = (length A, lma)"
    using abc_comp_first_steps_halt_eq b
    by(simp)
  then obtain nx where h1: "abc_steps_l (0, lm) (A [+] B) nx = (length A, lma)" ..   
  from c have "Q lma"
    using c unfolding abc_holds_for.simps
    by simp
  then obtain nb lmb where
    "abc_final (abc_steps_l (0, lma) B nb) B"
    and d: "abc_steps_l (0, lma) B nb = (length B, lmb)"
    and e: "S abc_holds_for (length B, lmb)"
    using B_halt unfolding abc_Hoare_halt_def
    by (metis (full_types) abc_final.simps abc_holds_for.simps prod.exhaust)
  have h2: "abc_steps_l (length A, lma) (A [+] B) nb = (length B + length A, lmb)"
    using d abc_comp_second_steps_eq
    by simp
  thus "\<exists>n. abc_final (abc_steps_l (0, lm) (A [+] B) n) (A [+] B) \<and>
    S abc_holds_for abc_steps_l (0, lm) (A [+] B) n"
    using h1 e
    by(rule_tac x = "nx + nb" in exI, simp add: abc_steps_add)
qed

lemma abc_unhalt_append_eq:
  assumes unhalt: "\<lbrace>P\<rbrace> (A::abc_prog) \<up>"
    and P: "P args"
  shows "abc_steps_l (0, args) (A [+] B) stp = abc_steps_l (0, args) A stp"
proof(induct stp)
  case 0
  thus "?case"
    by(simp add: abc_steps_l.simps)
next
  case (Suc stp)
  have ind: "abc_steps_l (0, args) (A [+] B) stp = abc_steps_l (0, args) A stp"
    by fact
  obtain s nl where a: "abc_steps_l (0, args) A stp = (s, nl)"
    by (metis prod.exhaust)
  then have b: "s < length A"
    using unhalt P
    apply(auto simp: abc_Hoare_unhalt_def)
    by (metis abc_notfinal.simps)
  thus "?case"
    using a ind
    by(simp add: abc_step_red2 abc_step_l.simps abc_fetch.simps nth_append abc_comp.simps)
qed

lemma abc_Hoare_plus_unhalt1: 
  "\<lbrace>P\<rbrace> (A::abc_prog) \<up> \<Longrightarrow> \<lbrace>P\<rbrace> (A [+] B) \<up>"
  apply(rule abc_Hoare_unhaltI)
  apply(subst abc_unhalt_append_eq,force,force)
  by (metis (mono_tags, lifting) abc_notfinal.elims(3) abc_notfinal.simps add_diff_inverse_nat 
      abc_Hoare_unhalt_def le_imp_less_Suc length_abc_comp not_less_eq order_refl trans_le_add1)

lemma notfinal_all_before:
  "\<lbrakk>abc_notfinal (abc_steps_l (0, args) A x) A; y\<le>x \<rbrakk>
  \<Longrightarrow> abc_notfinal (abc_steps_l (0, args) A y) A "
  apply(subgoal_tac "\<exists> d. x = y + d", auto)
   apply(cases "abc_steps_l (0, args) A y",simp)
   apply(rule classical, simp add: abc_steps_add leI halt_steps2)
  by arith

lemma abc_Hoare_plus_unhalt2':
  assumes unhalt: "\<lbrace>Q\<rbrace> (B::abc_prog) \<up>"
    and halt: "\<lbrace>P\<rbrace> (A::abc_prog) \<lbrace>Q\<rbrace>"
    and notnull: "A \<noteq> []"
    and P: "P args" 
  shows "abc_notfinal (abc_steps_l (0, args) (A [+] B) n) (A [+] B)"
proof -
  obtain st nl stp where a: "abc_final (abc_steps_l (0, args) A stp) A"
    and b: "Q abc_holds_for (length A, nl)"
    and c: "abc_steps_l (0, args) A stp = (st, nl)"
    using halt P unfolding abc_Hoare_halt_def
    by (metis abc_holds_for.simps prod.exhaust)
  obtain stpa where d: 
    "abc_notfinal (abc_steps_l (0, args) A stpa) A \<and> abc_final (abc_steps_l (0, args) A (Suc stpa)) A"
    using abc_before_final[of args A stp,OF a notnull] by metis
  thus "?thesis"
  proof(cases "n < Suc stpa")
    case True
    have h: "n < Suc stpa" by fact
    then have "abc_notfinal (abc_steps_l (0, args) A n) A"
      using d
      by(rule_tac notfinal_all_before, auto)
    moreover then have "abc_steps_l (0, args) (A [+] B) n = abc_steps_l (0, args) A n"
      using notnull
      by(rule_tac abc_comp_first_steps_eq_pre, simp_all)
    ultimately show "?thesis"
      by(case_tac "abc_steps_l (0, args) A n", simp)
  next
    case False
    have "\<not> n < Suc stpa" by fact
    then obtain d where i1: "n = Suc stpa + d"
      by (metis add_Suc less_iff_Suc_add not_less_eq)
    have "abc_steps_l (0, args) A (Suc stpa) = (length A, nl)"
      using d a c
      apply(case_tac "abc_steps_l (0, args) A stp", simp add: equal_when_halt)
      by(case_tac "abc_steps_l (0, args) A (Suc stpa)", simp add: equal_when_halt)
    moreover have  "abc_steps_l (0, args) (A [+] B) stpa = abc_steps_l (0, args) A stpa"
      using notnull d
      by(rule_tac abc_comp_first_steps_eq_pre, simp_all)
    ultimately have i2: "abc_steps_l (0, args) (A [+] B) (Suc stpa) = (length A, nl)"
      using d
      apply(case_tac "abc_steps_l (0, args) A stpa", simp)
      by(simp add: abc_step_red2 abc_steps_l.simps abc_fetch.simps abc_comp.simps nth_append)
    obtain s' nl' where i3:"abc_steps_l (0, nl) B d = (s', nl')"
      by (metis prod.exhaust)
    then have i4: "abc_steps_l (0, args) (A [+] B) (Suc stpa + d) = (length A + s', nl')"
      using i2  apply(simp only: abc_steps_add)
      using abc_comp_second_steps_eq[of nl B d s' nl']
      by simp
    moreover have "s' < length B"
      using unhalt b i3
      apply(simp add: abc_Hoare_unhalt_def)
      apply(erule_tac x = nl in allE, simp)
      by(erule_tac x = d in allE, simp)
    ultimately show "?thesis"
      using i1
      by(simp)
  qed
qed

lemma abc_comp_null_left[simp]: "[] [+] A = A"
proof(induct A)
  case (Cons a A)
  then show ?case 
    apply(cases a)
    by(auto simp: abc_comp.simps abc_shift.simps)
qed (auto simp: abc_comp.simps abc_shift.simps)

lemma abc_comp_null_right[simp]: "A [+] [] = A"
proof(induct A)
  case (Cons a A)
  then show ?case 
    apply(cases a)
    by(auto simp: abc_comp.simps abc_shift.simps)
qed (auto simp: abc_comp.simps abc_shift.simps)

lemma abc_Hoare_plus_unhalt2:
  "\<lbrakk>\<lbrace>Q\<rbrace> (B::abc_prog)\<up>; \<lbrace>P\<rbrace> (A::abc_prog) \<lbrace>Q\<rbrace>\<rbrakk>\<Longrightarrow> \<lbrace>P\<rbrace> (A [+] B) \<up>"
  apply(case_tac "A = []")
   apply(simp add: abc_Hoare_halt_def abc_Hoare_unhalt_def abc_exec_null)
  apply(rule_tac abc_Hoare_unhaltI)
  apply(erule_tac abc_Hoare_plus_unhalt2', simp)
   apply(simp, simp)
  done

end
