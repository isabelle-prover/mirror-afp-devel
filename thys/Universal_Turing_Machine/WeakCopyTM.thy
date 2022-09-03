(* Title: thys/WeakCopyTM.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten

   Cleanup of proofs
   Author: Franz Regensburger (FABR) 02/2022
 *)

subsection \<open>Machines that duplicate a single Numeral\<close>

subsubsection \<open>A Turing machine that duplicates its input if the input is a single numeral\<close>

text\<open>The Machine WeakCopyTM does not check the number of its arguments on the initial tape.
If it is provided a single numeral it does a perfect job. However, if it gets no or more than
 one argument, it does not complain but produces some result.\<close>

theory WeakCopyTM
  imports
    Turing_HaltingConditions
begin

declare adjust.simps[simp del]

(* ---------- tm_copy_begin_orig ---------- *)

(*
let
tm_copy_begin_orig = from_raw [
    (WB,0),(R,2),
    (R,3),(R,2),
    (WO,3),(L,4),
    (L,4),(L,0) ]
*)

definition 
  tm_copy_begin_orig :: "instr list"
  where
    "tm_copy_begin_orig \<equiv>
       [(WB,0),(R,2), (R,3),(R,2), (WO,3),(L,4), (L,4),(L,0)]"

fun 
  inv_begin0 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin4 :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_begin0 n (l, r) = ((n > 1 \<and> (l, r) = (Oc \<up> (n - 2), [Oc, Oc, Bk, Oc])) \<or>   
                          (n = 1 \<and> (l, r) = ([], [Bk, Oc, Bk, Oc])))"
  | "inv_begin1 n (l, r) = ((l, r) = ([], Oc \<up> n))"
  | "inv_begin2 n (l, r) = (\<exists> i j. i > 0 \<and> i + j = n \<and> (l, r) = (Oc \<up> i, Oc \<up> j))"
  | "inv_begin3 n (l, r) = (n > 0 \<and> (l, tl r) = (Bk # Oc \<up> n, []))"
  | "inv_begin4 n (l, r) = (n > 0 \<and> (l, r) = (Oc \<up> n, [Bk, Oc]) \<or> (l, r) = (Oc \<up> (n - 1), [Oc, Bk, Oc]))"

fun inv_begin :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_begin n (s, tap) = 
        (if s = 0 then inv_begin0 n tap else
         if s = 1 then inv_begin1 n tap else
         if s = 2 then inv_begin2 n tap else
         if s = 3 then inv_begin3 n tap else
         if s = 4 then inv_begin4 n tap 
         else False)"

lemma inv_begin_step_E: "\<lbrakk>0 < i; 0 < j\<rbrakk> \<Longrightarrow> 
  \<exists>ia>0. ia + j - Suc 0 = i + j \<and> Oc # Oc \<up> i = Oc \<up> ia"
  by (rule_tac x = "Suc i" in exI, simp)

lemma inv_begin_step: 
  assumes "inv_begin n cf"
    and "n > 0"
  shows "inv_begin n (step0 cf tm_copy_begin_orig)"
  using assms
  unfolding tm_copy_begin_orig_def
  apply(cases cf)
  apply(auto simp: numeral_eqs_upto_12 split: if_splits elim:inv_begin_step_E)
  apply(cases "hd (snd (snd cf))";cases "(snd (snd cf))",auto)
  done

lemma inv_begin_steps: 
  assumes "inv_begin n cf"
    and "n > 0"
  shows "inv_begin n (steps0 cf tm_copy_begin_orig stp)"
  apply(induct stp)
   apply(simp add: assms)
  apply(auto simp del: steps.simps)
  apply(rule_tac inv_begin_step)
   apply(simp_all add: assms)
  done

lemma begin_partial_correctness:
  assumes "is_final (steps0 (1, [], Oc \<up> n) tm_copy_begin_orig stp)"
  shows "0 < n \<Longrightarrow> \<lbrace>inv_begin1 n\<rbrace> tm_copy_begin_orig \<lbrace>inv_begin0 n\<rbrace>"
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n" "inv_begin1 n (l, r)"
  have "inv_begin n (steps0 (1, [], Oc \<up> n) tm_copy_begin_orig stp)"
    using h by (rule_tac inv_begin_steps) (simp_all)
  then show
    "\<exists>stp. is_final (steps0 (1, l, r) tm_copy_begin_orig stp) \<and> 
    inv_begin0 n holds_for steps (1, l, r) (tm_copy_begin_orig, 0) stp"
    using h assms
    apply(rule_tac x = stp in exI)
    apply(case_tac "(steps0 (1, [], Oc \<up> n) tm_copy_begin_orig stp)", simp)
    done
qed

fun measure_begin_state :: "config \<Rightarrow> nat"
  where
    "measure_begin_state (s, l, r) = (if s = 0 then 0 else 5 - s)"

fun measure_begin_step :: "config \<Rightarrow> nat"
  where
    "measure_begin_step (s, l, r) = 
        (if s = 2 then length r else
         if s = 3 then (if r = [] \<or> r = [Bk] then 1 else 0) else
         if s = 4 then length l 
         else 0)"

definition
  "measure_begin = measures [measure_begin_state, measure_begin_step]"

lemma wf_measure_begin:
  shows "wf measure_begin" 
  unfolding measure_begin_def 
  by auto

lemma measure_begin_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_begin\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_begin
  by (metis wf_iff_no_infinite_down_chain)

lemma begin_halts: 
  assumes h: "x > 0"
  shows "\<exists> stp. is_final (steps0 (1, [], Oc \<up> x) tm_copy_begin_orig stp)"
proof (induct rule: measure_begin_induct) 
  case (Step n)
  have "\<not> is_final (steps0 (1, [], Oc \<up> x) tm_copy_begin_orig n)" by fact
  moreover
  have "inv_begin x (steps0 (1, [], Oc \<up> x) tm_copy_begin_orig n)"
    by (rule_tac inv_begin_steps) (simp_all add:  h)
  moreover
  obtain s l r where eq: "(steps0 (1, [], Oc \<up> x) tm_copy_begin_orig n) = (s, l, r)"
    by (metis measure_begin_state.cases)
  ultimately 
  have "(step0 (s, l, r) tm_copy_begin_orig, s, l, r) \<in> measure_begin"
    apply(auto simp: measure_begin_def tm_copy_begin_orig_def numeral_eqs_upto_12 split: if_splits)
    apply(subgoal_tac "r = [Oc]")
     apply(auto)
    by (metis cell.exhaust list.exhaust list.sel(3))
  then 
  show "(steps0 (1, [], Oc \<up> x) tm_copy_begin_orig (Suc n), steps0 (1, [], Oc \<up> x) tm_copy_begin_orig n) \<in> measure_begin"
    using eq by (simp only: step_red)
qed


lemma begin_correct:
  shows "0 < n \<Longrightarrow> \<lbrace>inv_begin1 n\<rbrace> tm_copy_begin_orig \<lbrace>inv_begin0 n\<rbrace>"
  using begin_partial_correctness begin_halts by blast

lemma begin_correct2:
  assumes "0 < (n::nat)"
  shows "\<lbrace>\<lambda>tap. tap = ([]::cell list, Oc \<up> n)\<rbrace>
         tm_copy_begin_orig
         \<lbrace>\<lambda>tap. (n > 1 \<and> tap = (Oc \<up> (n - 2), [Oc, Oc, Bk, Oc])) \<or>   
                (n = 1 \<and> tap = ([]::cell list, [Bk, Oc, Bk, Oc])) \<rbrace>"
proof -
  from assms have "\<lbrace>inv_begin1 n\<rbrace> tm_copy_begin_orig \<lbrace>inv_begin0 n\<rbrace>"
    using begin_partial_correctness begin_halts by blast
  with assms have "\<lbrace>\<lambda>tap. tap = ([]::cell list, Oc \<up> n)\<rbrace> tm_copy_begin_orig \<lbrace>inv_begin0 n\<rbrace>"
    using Hoare_haltE Hoare_haltI inv_begin1.simps by presburger    
  with assms show ?thesis
    by (smt Hoare_haltI Hoare_halt_def Pair_inject
        holds_for.elims(2) holds_for.simps inv_begin0.simps is_final.elims(2))
qed

(* ---------- tm_copy_loop_orig ---------- *)

(* Delete some theorems from the simpset *)

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]


(*
let
tm_copy_loop_orig = from_raw [
    (R,0),(R,2),
    (R,3),(WB,2),
    (R,3),(R,4),
    (WO,5),(R,4),
    (L,6),(L,5),
    (L,6),(L,1) ]

*)

definition 
  tm_copy_loop_orig :: "instr list"
  where
    "tm_copy_loop_orig \<equiv>
    [ (R, 0),(R, 2), (R, 3),(WB, 2), (R, 3),(R, 4), (WO, 5),(R, 4), (L, 6),(L, 5), (L, 6),(L, 1) ]"

fun 
  inv_loop1_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop1_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_loop1_loop n (l, r) = (\<exists> i j. i + j + 1 = n \<and> (l, r) = (Oc\<up>i, Oc#Oc#Bk\<up>j @ Oc\<up>j) \<and> j > 0)"
  | "inv_loop1_exit n (l, r) = (0 < n \<and> (l, r) = ([], Bk#Oc#Bk\<up>n @ Oc\<up>n))"
  | "inv_loop5_loop x (l, r) = 
     (\<exists> i j k t. i + j = Suc x \<and> i > 0 \<and> j > 0 \<and> k + t = j \<and> t > 0 \<and> (l, r) = (Oc\<up>k@Bk\<up>j@Oc\<up>i, Oc\<up>t))"
  | "inv_loop5_exit x (l, r) = 
     (\<exists> i j. i + j = Suc x \<and> i > 0 \<and> j > 0 \<and> (l, r) = (Bk\<up>(j - 1)@Oc\<up>i, Bk # Oc\<up>j))"
  | "inv_loop6_loop x (l, r) = 
     (\<exists> i j k t. i + j = Suc x \<and> i > 0 \<and> k + t + 1 = j \<and> (l, r) = (Bk\<up>k @ Oc\<up>i, Bk\<up>(Suc t) @ Oc\<up>j))"
  | "inv_loop6_exit x (l, r) = 
     (\<exists> i j. i + j = x \<and> j > 0 \<and> (l, r) = (Oc\<up>i, Oc#Bk\<up>j @ Oc\<up>j))"

fun 
  inv_loop0 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop4 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6 :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_loop0 n (l, r) =  (0 < n \<and> (l, r) = ([Bk], Oc # Bk\<up>n @ Oc\<up>n))"
  | "inv_loop1 n (l, r) = (inv_loop1_loop n (l, r) \<or> inv_loop1_exit n (l, r))"
  | "inv_loop2 n (l, r) = (\<exists> i j any. i + j = n \<and> n > 0 \<and> i > 0 \<and> j > 0 \<and> (l, r) = (Oc\<up>i, any#Bk\<up>j@Oc\<up>j))"
  | "inv_loop3 n (l, r) = 
     (\<exists> i j k t. i + j = n \<and> i > 0 \<and> j > 0 \<and>  k + t = Suc j \<and> (l, r) = (Bk\<up>k@Oc\<up>i, Bk\<up>t@Oc\<up>j))"
  | "inv_loop4 n (l, r) = 
     (\<exists> i j k t. i + j = n \<and> i > 0 \<and> j > 0 \<and>  k + t = j \<and> (l, r) = (Oc\<up>k @ Bk\<up>(Suc j)@Oc\<up>i, Oc\<up>t))"
  | "inv_loop5 n (l, r) = (inv_loop5_loop n (l, r) \<or> inv_loop5_exit n (l, r))"
  | "inv_loop6 n (l, r) = (inv_loop6_loop n (l, r) \<or> inv_loop6_exit n (l, r))"

fun inv_loop :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_loop x (s, l, r) = 
         (if s = 0 then inv_loop0 x (l, r)
          else if s = 1 then inv_loop1 x (l, r)
          else if s = 2 then inv_loop2 x (l, r)
          else if s = 3 then inv_loop3 x (l, r)
          else if s = 4 then inv_loop4 x (l, r)
          else if s = 5 then inv_loop5 x (l, r)
          else if s = 6 then inv_loop6 x (l, r)
          else False)"

declare inv_loop.simps[simp del] inv_loop1.simps[simp del]
  inv_loop2.simps[simp del] inv_loop3.simps[simp del] 
  inv_loop4.simps[simp del] inv_loop5.simps[simp del] 
  inv_loop6.simps[simp del]

lemma inv_loop3_Bk_empty_via_2[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, [])"
  by (auto simp: inv_loop2.simps inv_loop3.simps)

lemma inv_loop3_Bk_empty[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, [])"
  by (auto simp: inv_loop3.simps)

lemma inv_loop5_Oc_empty_via_4[elim]: "\<lbrakk>0 < x; inv_loop4 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop5 x (b, [Oc])"
  by(auto simp: inv_loop4.simps inv_loop5.simps;force)

lemma inv_loop1_Bk[elim]: "\<lbrakk>0 < x; inv_loop1 x (b, Bk # list)\<rbrakk> \<Longrightarrow> list = Oc # Bk \<up> x @ Oc \<up> x"
  by (auto simp: inv_loop1.simps)

lemma inv_loop3_Bk_via_2[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, list)"
  by(auto simp: inv_loop2.simps inv_loop3.simps;force)

lemma inv_loop3_Bk_move[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, list)"
  apply(auto simp: inv_loop3.simps)
   apply (rename_tac i j k t)
   apply(rule_tac [!] x = i in exI, 
      rule_tac [!] x = j in exI, simp_all)
   apply(case_tac [!] t, auto)
  done

lemma inv_loop5_Oc_via_4_Bk[elim]: "\<lbrakk>0 < x; inv_loop4 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop5 x (b, Oc # list)"
  by (auto simp: inv_loop4.simps inv_loop5.simps)

lemma inv_loop6_Bk_via_5[elim]: "\<lbrakk>0 < x; inv_loop5 x ([], Bk # list)\<rbrakk> \<Longrightarrow> inv_loop6 x ([], Bk # Bk # list)"
  by (auto simp: inv_loop6.simps inv_loop5.simps)

lemma inv_loop5_loop_no_Bk[simp]: "inv_loop5_loop x (b, Bk # list) = False"
  by (auto simp: inv_loop5.simps)

lemma inv_loop6_exit_no_Bk[simp]: "inv_loop6_exit x (b, Bk # list) = False"
  by (auto simp: inv_loop6.simps)

declare inv_loop5_loop.simps[simp del]  inv_loop5_exit.simps[simp del]
  inv_loop6_loop.simps[simp del]  inv_loop6_exit.simps[simp del]

lemma inv_loop6_loopBk_via_5[elim]:"\<lbrakk>0 < x; inv_loop5_exit x (b, Bk # list); b \<noteq> []; hd b = Bk\<rbrakk> 
          \<Longrightarrow> inv_loop6_loop x (tl b, Bk # Bk # list)"
  apply(simp only: inv_loop5_exit.simps inv_loop6_loop.simps )
  apply(erule_tac exE)+
  apply(rename_tac i j)
  apply(rule_tac x = i in exI, 
      rule_tac x = j in exI,
      rule_tac x = "j - Suc (Suc 0)" in exI, 
      rule_tac x = "Suc 0" in exI, auto)
   apply(case_tac [!] j, simp_all)
   apply(case_tac [!] "j-1", simp_all)
  done

lemma inv_loop6_loop_no_Oc_Bk[simp]: "inv_loop6_loop x (b, Oc # Bk # list) = False"
  by (auto simp: inv_loop6_loop.simps)

lemma inv_loop6_exit_Oc_Bk_via_5[elim]: "\<lbrakk>x > 0; inv_loop5_exit x (b, Bk # list); b \<noteq> []; hd b = Oc\<rbrakk> \<Longrightarrow> 
  inv_loop6_exit x (tl b, Oc # Bk # list)"
  apply(simp only: inv_loop5_exit.simps inv_loop6_exit.simps)
  apply(erule_tac exE)+
  apply(rule_tac x = "x - 1" in exI, rule_tac x = 1 in exI, simp)
  apply(rename_tac i j)
  apply(case_tac j;case_tac "j-1", auto)
  done

lemma inv_loop6_Bk_tail_via_5[elim]: "\<lbrakk>0 < x; inv_loop5 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop6 x (tl b, hd b # Bk # list)"
  apply(simp add: inv_loop5.simps inv_loop6.simps)
  apply(cases "hd b", simp_all, auto)
  done

lemma inv_loop6_loop_Bk_Bk_drop[elim]: "\<lbrakk>0 < x; inv_loop6_loop x (b, Bk # list); b \<noteq> []; hd b = Bk\<rbrakk>
              \<Longrightarrow> inv_loop6_loop x (tl b, Bk # Bk # list)"
  apply(simp only: inv_loop6_loop.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI, rule_tac x = j in exI, 
      rule_tac x = "k - 1" in exI, rule_tac x = "Suc t" in exI, auto)
   apply(case_tac [!] k, auto)
  done

lemma inv_loop6_exit_Oc_Bk_via_loop6[elim]: "\<lbrakk>0 < x; inv_loop6_loop x (b, Bk # list); b \<noteq> []; hd b = Oc\<rbrakk> 
        \<Longrightarrow> inv_loop6_exit x (tl b, Oc # Bk # list)"
  apply(simp only: inv_loop6_loop.simps inv_loop6_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = "i - 1" in exI, rule_tac x = j in exI, auto)
   apply(case_tac [!] k, auto)
  done

lemma inv_loop6_Bk_tail[elim]: "\<lbrakk>0 < x; inv_loop6 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop6 x (tl b, hd b # Bk # list)"
  apply(simp add: inv_loop6.simps)
  apply(case_tac "hd b", simp_all, auto)
  done

lemma inv_loop2_Oc_via_1[elim]: "\<lbrakk>0 < x; inv_loop1 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop2 x (Oc # b, list)"
  apply(auto simp: inv_loop1.simps inv_loop2.simps,force)
  done

lemma inv_loop2_Bk_via_Oc[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop2 x (b, Bk # list)"
  by (auto simp: inv_loop2.simps)

lemma inv_loop4_Oc_via_3[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop4 x (Oc # b, list)"
  apply(auto simp: inv_loop3.simps inv_loop4.simps)
   apply(rename_tac i j)
   apply(rule_tac [!] x = i in exI, auto)
   apply(rule_tac [!] x = "Suc 0" in exI, rule_tac [!] x = "j - 1" in exI)
   apply(case_tac [!] j, auto)
  done

lemma inv_loop4_Oc_move[elim]:
  assumes "0 < x" "inv_loop4 x (b, Oc # list)"
  shows "inv_loop4 x (Oc # b, list)"
proof -
  from assms[unfolded inv_loop4.simps] obtain i j k t where
    "i + j = x"
    "0 < i" "0 < j" "k + t = j" "(b, Oc # list) = (Oc \<up> k @ Bk \<up> Suc j @ Oc \<up> i, Oc \<up> t)"
    by auto  
  thus ?thesis unfolding inv_loop4.simps
    apply(rule_tac [!] x = "i" in exI,rule_tac [!] x = "j" in exI)
    apply(rule_tac [!] x = "Suc k" in exI,rule_tac [!] x = "t - 1" in exI)
    by(cases t,auto)
qed

lemma inv_loop5_exit_no_Oc[simp]: "inv_loop5_exit x (b, Oc # list) = False"
  by (auto simp: inv_loop5_exit.simps)

lemma inv_loop5_exit_Bk_Oc_via_loop[elim]: " \<lbrakk>inv_loop5_loop x (b, Oc # list); b \<noteq> []; hd b = Bk\<rbrakk>
  \<Longrightarrow> inv_loop5_exit x (tl b, Bk # Oc # list)"
  apply(simp only: inv_loop5_loop.simps inv_loop5_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI)
  apply(case_tac k, auto)
  done

lemma inv_loop5_loop_Oc_Oc_drop[elim]: "\<lbrakk>inv_loop5_loop x (b, Oc # list); b \<noteq> []; hd b = Oc\<rbrakk> 
           \<Longrightarrow> inv_loop5_loop x (tl b, Oc # Oc # list)"
  apply(simp only:  inv_loop5_loop.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI, rule_tac x = j in exI)
  apply(rule_tac x = "k - 1" in exI, rule_tac x = "Suc t" in exI)
  apply(case_tac k, auto)
  done

lemma inv_loop5_Oc_tl[elim]: "\<lbrakk>inv_loop5 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop5 x (tl b, hd b # Oc # list)"
  apply(simp add: inv_loop5.simps)
  apply(cases "hd b", simp_all, auto)
  done

lemma inv_loop1_Bk_Oc_via_6[elim]: "\<lbrakk>0 < x; inv_loop6 x ([], Oc # list)\<rbrakk> \<Longrightarrow> inv_loop1 x ([], Bk # Oc # list)"
  by(auto simp: inv_loop6.simps inv_loop1.simps inv_loop6_loop.simps inv_loop6_exit.simps)

lemma inv_loop1_Oc_via_6[elim]: "\<lbrakk>0 < x; inv_loop6 x (b, Oc # list); b \<noteq> []\<rbrakk> 
           \<Longrightarrow> inv_loop1 x (tl b, hd b # Oc # list)"
  by(auto simp: inv_loop6.simps inv_loop1.simps inv_loop6_loop.simps inv_loop6_exit.simps)


lemma inv_loop_nonempty[simp]:
  "inv_loop1 x (b, []) = False"
  "inv_loop2 x ([], b) = False"
  "inv_loop2 x (l', []) = False"
  "inv_loop3 x (b, []) = False"
  "inv_loop4 x ([], b) = False"
  "inv_loop5 x ([], list) = False"
  "inv_loop6 x ([], Bk # xs) = False"
  by (auto simp: inv_loop1.simps inv_loop2.simps inv_loop3.simps inv_loop4.simps 
      inv_loop5.simps inv_loop6.simps inv_loop5_exit.simps inv_loop5_loop.simps
      inv_loop6_loop.simps)

lemma inv_loop_nonemptyE[elim]:
  "\<lbrakk>inv_loop5 x (b, [])\<rbrakk> \<Longrightarrow> RR" "inv_loop6 x (b, []) \<Longrightarrow> RR" 
  "\<lbrakk>inv_loop1 x (b, Bk # list)\<rbrakk> \<Longrightarrow> b = []"
  by (auto simp: inv_loop4.simps inv_loop5.simps inv_loop5_exit.simps inv_loop5_loop.simps
      inv_loop6.simps inv_loop6_exit.simps inv_loop6_loop.simps inv_loop1.simps)

lemma inv_loop6_Bk_Bk_drop[elim]: "\<lbrakk>inv_loop6 x ([], Bk # list)\<rbrakk> \<Longrightarrow> inv_loop6 x ([], Bk # Bk # list)"
  by (simp)

lemma inv_loop_step: 
  "\<lbrakk>inv_loop x cf; x > 0\<rbrakk> \<Longrightarrow> inv_loop x (step cf (tm_copy_loop_orig, 0))"
  apply(cases cf, cases "snd (snd cf)"; cases "hd (snd (snd cf))")
     apply(auto simp: inv_loop.simps step.simps tm_copy_loop_orig_def numeral_eqs_upto_12 split: if_splits)
  done

lemma inv_loop_steps:
  "\<lbrakk>inv_loop x cf; x > 0\<rbrakk> \<Longrightarrow> inv_loop x (steps cf (tm_copy_loop_orig, 0) stp)"
  apply(induct stp, simp add: steps.simps, simp)
  apply(erule_tac inv_loop_step, simp)
  done

fun loop_stage :: "config \<Rightarrow> nat"
  where
    "loop_stage (s, l, r) = (if s = 0 then 0
                           else (Suc (length (takeWhile (\<lambda>a. a = Oc) (rev l @ r)))))"

fun loop_state :: "config \<Rightarrow> nat"
  where
    "loop_state (s, l, r) = (if s = 2 \<and> hd r = Oc then 0
                           else if s = 1 then 1
                           else 10 - s)"

fun loop_step :: "config \<Rightarrow> nat"
  where
    "loop_step (s, l, r) = (if s = 3 then length r
                          else if s = 4 then length r
                          else if s = 5 then length l 
                          else if s = 6 then length l
                          else 0)"

definition measure_loop :: "(config \<times> config) set"
  where
    "measure_loop = measures [loop_stage, loop_state, loop_step]"

lemma wf_measure_loop: "wf measure_loop"
  unfolding measure_loop_def
  by (auto)

lemma measure_loop_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_loop\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_loop
  by (metis wf_iff_no_infinite_down_chain)

lemma inv_loop4_not_just_Oc[elim]: 
  "\<lbrakk>inv_loop4 x (l', []);
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ [Oc])) \<noteq> 
  length (takeWhile (\<lambda>a. a = Oc) (rev l'))\<rbrakk>
  \<Longrightarrow> RR"
  "\<lbrakk>inv_loop4 x (l', Bk # list);
   length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Oc # list)) \<noteq> 
    length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list))\<rbrakk>
    \<Longrightarrow> RR"
   apply(auto simp: inv_loop4.simps)
  apply(rename_tac i j)
  apply(case_tac [!] j, simp_all add: List.takeWhile_tail)
  done

lemma takeWhile_replicate_append: 
  "P a \<Longrightarrow> takeWhile P (a\<up>x @ ys) = a\<up>x @ takeWhile P ys"
  by (induct x, auto)

lemma takeWhile_replicate: 
  "P a \<Longrightarrow> takeWhile P (a\<up>x) = a\<up>x"
  by (induct x, auto)

lemma inv_loop5_Bk_E[elim]: 
  "\<lbrakk>inv_loop5 x (l', Bk # list); l' \<noteq> []; 
   length (takeWhile (\<lambda>a. a = Oc) (rev (tl l') @ hd l' # Bk # list)) \<noteq>
   length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list))\<rbrakk>
   \<Longrightarrow> RR"
  apply(cases "length list";cases "length list - 1"
      ,auto simp: inv_loop5.simps inv_loop5_exit.simps
      takeWhile_replicate_append takeWhile_replicate)
   apply(cases "length list - 2"; force simp add: List.takeWhile_tail)+
  done

lemma inv_loop1_hd_Oc[elim]: "\<lbrakk>inv_loop1 x (l', Oc # list)\<rbrakk> \<Longrightarrow> hd list = Oc"
  by (auto simp: inv_loop1.simps)

lemma inv_loop6_not_just_Bk[dest!]: 
  "\<lbrakk>length (takeWhile P (rev (tl l') @ hd l' # list)) \<noteq> 
  length (takeWhile P (rev l' @ list))\<rbrakk>
  \<Longrightarrow> l' = []"
  apply(cases l', simp_all)
  done

lemma inv_loop2_OcE[elim]:
  "\<lbrakk>inv_loop2 x (l', Oc # list); l' \<noteq> []\<rbrakk> \<Longrightarrow> 
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list)) <
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Oc # list))"
  apply(auto simp: inv_loop2.simps takeWhile_tail takeWhile_replicate_append
      takeWhile_replicate)
  done

lemma loop_halts: 
  assumes h: "n > 0" "inv_loop n (1, l, r)"
  shows "\<exists> stp. is_final (steps0 (1, l, r) tm_copy_loop_orig stp)"
proof (induct rule: measure_loop_induct) 
  case (Step stp)
  have "\<not> is_final (steps0 (1, l, r) tm_copy_loop_orig stp)" by fact
  moreover
  have "inv_loop n (steps0 (1, l, r) tm_copy_loop_orig stp)"
    by (rule_tac inv_loop_steps) (simp_all only: h)
  moreover
  obtain s l' r' where eq: "(steps0 (1, l, r) tm_copy_loop_orig stp) = (s, l', r')"
    by (metis measure_begin_state.cases)
  ultimately 
  have "(step0 (s, l', r') tm_copy_loop_orig, s, l', r') \<in> measure_loop"
    using h(1)
    apply(cases r';cases "hd r'")
    apply(auto simp: inv_loop.simps step.simps tm_copy_loop_orig_def numeral_eqs_upto_12 measure_loop_def split: if_splits)
    done
  then 
  show "(steps0 (1, l, r) tm_copy_loop_orig (Suc stp), steps0 (1, l, r) tm_copy_loop_orig stp) \<in> measure_loop"
    using eq by (simp only: step_red)
qed

lemma loop_correct:
  assumes "0 < n"
  shows "\<lbrace>inv_loop1 n\<rbrace> tm_copy_loop_orig \<lbrace>inv_loop0 n\<rbrace>"
  using assms
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n" "inv_loop1 n (l, r)"
  then obtain stp where k: "is_final (steps0 (1, l, r) tm_copy_loop_orig stp)" 
    using loop_halts
    apply(simp add: inv_loop.simps)
    apply(blast)
    done
  moreover
  have "inv_loop n (steps0 (1, l, r) tm_copy_loop_orig stp)"
    using h 
    by (rule_tac inv_loop_steps) (simp_all add: inv_loop.simps)
  ultimately show
    "\<exists>stp. is_final (steps0 (1, l, r) tm_copy_loop_orig stp) \<and> 
    inv_loop0 n holds_for steps0 (1, l, r) tm_copy_loop_orig stp"
    using h(1) 
    apply(rule_tac x = stp in exI)
    apply(case_tac "(steps0 (1, l, r) tm_copy_loop_orig stp)")
    apply(simp add: inv_loop.simps)
    done
qed


(* ---------- tm_copy_end ---------- *)

(*
let
tm_copy_end_orig = from_raw [
  (L,0),(R,2),
  (WO,3),(L,4),
  (R,2),(R,2),
  (L,5),(WB,4),
  (R,0),(L,5)
  ]

let
tm_copy_end_new = from_raw [
  (R,0),(R,2),    -- changed action for Bk from (L,0) to (R,0)
  (WO,3),(L,4),
  (R,2),(R,2),
  (L,5),(WB,4),
  (R,0),(L,5)
  ]
*)

definition 
  tm_copy_end_orig :: "instr list"
  where
    "tm_copy_end_orig \<equiv>
    [ (L, 0),(R, 2), (WO, 3),(L, 4), (R, 2),(R, 2), (L, 5),(WB, 4), (R, 0),(L, 5) ]"

definition 
  tm_copy_end_new :: "instr list"
  where
    "tm_copy_end_new \<equiv>
    [ (R, 0),(R, 2), (WO, 3),(L, 4), (R, 2),(R, 2), (L, 5),(WB, 4), (R, 0),(L, 5) ]"

fun
  inv_end5_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end5_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" 
  where  
    "inv_end5_loop x (l, r) = 
     (\<exists> i j. i + j = x \<and> x > 0 \<and> j > 0 \<and> l = Oc\<up>i @ [Bk] \<and> r = Oc\<up>j @ Bk # Oc\<up>x)"
  | "inv_end5_exit x (l, r) = (x > 0 \<and> l = [] \<and> r = Bk # Oc\<up>x @ Bk # Oc\<up>x)"

fun 
  inv_end0 :: "nat \<Rightarrow> tape \<Rightarrow>  bool" and
  inv_end1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end4 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and 
  inv_end5 :: "nat \<Rightarrow> tape \<Rightarrow> bool" 
  where
    "inv_end0 n (l, r) = (n > 0 \<and> (l, r) = ([Bk], Oc\<up>n @ Bk # Oc\<up>n))"
  | "inv_end1 n (l, r) = (n > 0 \<and> (l, r) = ([Bk], Oc # Bk\<up>n @ Oc\<up>n))"
  | "inv_end2 n (l, r) = (\<exists> i j. i + j = Suc n \<and> n > 0 \<and> l = Oc\<up>i @ [Bk] \<and> r = Bk\<up>j @ Oc\<up>n)"
  | "inv_end3 n (l, r) =
     (\<exists> i j. n > 0 \<and> i + j = n \<and> l = Oc\<up>i @ [Bk] \<and> r = Oc # Bk\<up>j@ Oc\<up>n)"
  | "inv_end4 n (l, r) = (\<exists> any. n > 0 \<and> l = Oc\<up>n @ [Bk] \<and> r = any#Oc\<up>n)"
  | "inv_end5 n (l, r) = (inv_end5_loop n (l, r) \<or> inv_end5_exit n (l, r))"

fun 
  inv_end :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_end n (s, l, r) = (if s = 0 then inv_end0 n (l, r)
                          else if s = 1 then inv_end1 n (l, r)
                          else if s = 2 then inv_end2 n (l, r)
                          else if s = 3 then inv_end3 n (l, r)
                          else if s = 4 then inv_end4 n (l, r)
                          else if s = 5 then inv_end5 n (l, r)
                          else False)"

declare inv_end.simps[simp del] inv_end1.simps[simp del]
  inv_end0.simps[simp del] inv_end2.simps[simp del]
  inv_end3.simps[simp del] inv_end4.simps[simp del]
  inv_end5.simps[simp del]

lemma inv_end_nonempty[simp]:
  "inv_end1 x (b, []) = False"
  "inv_end1 x ([], list) = False"
  "inv_end2 x (b, []) = False"
  "inv_end3 x (b, []) = False"
  "inv_end4 x (b, []) = False"
  "inv_end5 x (b, []) = False"
  "inv_end5 x ([], Oc # list) = False"
  by (auto simp: inv_end1.simps inv_end2.simps inv_end3.simps inv_end4.simps inv_end5.simps)

lemma inv_end0_Bk_via_1[elim]: "\<lbrakk>0 < x; inv_end1 x (b, Bk # list); b \<noteq> []\<rbrakk>
  \<Longrightarrow> inv_end0 x (tl b, hd b # Bk # list)"
  by (auto simp: inv_end1.simps inv_end0.simps)

lemma inv_end3_Oc_via_2[elim]: "\<lbrakk>0 < x; inv_end2 x (b, Bk # list)\<rbrakk> 
  \<Longrightarrow> inv_end3 x (b, Oc # list)"
  apply(auto simp: inv_end2.simps inv_end3.simps)
  by (metis Cons_replicate_eq One_nat_def Suc_inject Suc_pred add_Suc_right cell.distinct(1)
      empty_replicate list.sel(3) neq0_conv self_append_conv2 tl_append2 tl_replicate)

lemma inv_end2_Bk_via_3[elim]: "\<lbrakk>0 < x; inv_end3 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Bk # b, list)"
  by (auto simp: inv_end2.simps inv_end3.simps)

lemma inv_end5_Bk_via_4[elim]: "\<lbrakk>0 < x; inv_end4 x ([], Bk # list)\<rbrakk> \<Longrightarrow> 
  inv_end5 x ([], Bk # Bk # list)"
  by (auto simp: inv_end4.simps inv_end5.simps)

lemma inv_end5_Bk_tail_via_4[elim]: "\<lbrakk>0 < x; inv_end4 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> 
  inv_end5 x (tl b, hd b # Bk # list)"
  apply(auto simp: inv_end4.simps inv_end5.simps)
  apply(rule_tac x = 1 in exI, simp)
  done

lemma inv_end0_Bk_via_5[elim]: "\<lbrakk>0 < x; inv_end5 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_end0 x (Bk # b, list)"
  by(auto simp: inv_end5.simps inv_end0.simps gr0_conv_Suc)

lemma inv_end2_Oc_via_1[elim]: "\<lbrakk>0 < x; inv_end1 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Oc # b, list)"
  by (auto simp: inv_end1.simps inv_end2.simps)

lemma inv_end4_Bk_Oc_via_2[elim]: "\<lbrakk>0 < x; inv_end2 x ([], Oc # list)\<rbrakk> \<Longrightarrow>
               inv_end4 x ([], Bk # Oc # list)"
  by (auto simp: inv_end2.simps inv_end4.simps)

lemma inv_end4_Oc_via_2[elim]:  "\<lbrakk>0 < x; inv_end2 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow>
  inv_end4 x (tl b, hd b # Oc # list)"
  by(auto simp: inv_end2.simps inv_end4.simps gr0_conv_Suc)

lemma inv_end2_Oc_via_3[elim]: "\<lbrakk>0 < x; inv_end3 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Oc # b, list)"
  by (auto simp: inv_end2.simps inv_end3.simps)

lemma inv_end4_Bk_via_Oc[elim]: "\<lbrakk>0 < x; inv_end4 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end4 x (b, Bk # list)"
  by (auto simp: inv_end2.simps inv_end4.simps)

lemma inv_end5_Bk_drop_Oc[elim]: "\<lbrakk>0 < x; inv_end5 x ([], Oc # list)\<rbrakk> \<Longrightarrow> inv_end5 x ([], Bk # Oc # list)"
  by (auto simp: inv_end2.simps inv_end5.simps)

declare inv_end5_loop.simps[simp del]
  inv_end5_exit.simps[simp del]

lemma inv_end5_exit_no_Oc[simp]: "inv_end5_exit x (b, Oc # list) = False"
  by (auto simp: inv_end5_exit.simps)

lemma inv_end5_loop_no_Bk_Oc[simp]: "inv_end5_loop x (tl b, Bk # Oc # list) = False"
  by (auto simp: inv_end5_loop.simps)

lemma inv_end5_exit_Bk_Oc_via_loop[elim]:
  "\<lbrakk>0 < x; inv_end5_loop x (b, Oc # list); b \<noteq> []; hd b = Bk\<rbrakk> \<Longrightarrow>
  inv_end5_exit x (tl b, Bk # Oc # list)"
  apply(auto simp: inv_end5_loop.simps inv_end5_exit.simps)
  using hd_replicate apply fastforce
  by (metis cell.distinct(1) hd_append2 hd_replicate list.sel(3) self_append_conv2
      split_head_repeat(2))

lemma inv_end5_loop_Oc_Oc_drop[elim]: 
  "\<lbrakk>0 < x; inv_end5_loop x (b, Oc # list); b \<noteq> []; hd b = Oc\<rbrakk> \<Longrightarrow>
  inv_end5_loop x (tl b, Oc # Oc # list)"
  apply(simp only: inv_end5_loop.simps inv_end5_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j)
  apply(rule_tac x = "i - 1" in exI, 
      rule_tac x = "Suc j" in exI, auto)
   apply(case_tac [!] i, simp_all)
  done

lemma inv_end5_Oc_tail[elim]: "\<lbrakk>0 < x; inv_end5 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow> 
  inv_end5 x (tl b, hd b # Oc # list)"
  apply(simp add: inv_end2.simps inv_end5.simps)
  apply(case_tac "hd b", simp_all, auto)
  done

lemma inv_end_step:
  "\<lbrakk>x > 0; inv_end x cf\<rbrakk> \<Longrightarrow> inv_end x (step cf (tm_copy_end_new, 0))"
  apply(cases cf, cases "snd (snd cf)"; cases "hd (snd (snd cf))")
  apply(auto simp: inv_end.simps step.simps tm_copy_end_new_def numeral_eqs_upto_12 split: if_splits)
  apply (simp add: inv_end1.simps)
  done

lemma inv_end_steps:
  "\<lbrakk>x > 0; inv_end x cf\<rbrakk> \<Longrightarrow> inv_end x (steps cf (tm_copy_end_new, 0) stp)"
  apply(induct stp, simp add:steps.simps, simp)
  apply(erule_tac inv_end_step, simp)
  done

fun end_state :: "config \<Rightarrow> nat"
  where
    "end_state (s, l, r) = 
       (if s = 0 then 0
        else if s = 1 then 5
        else if s = 2 \<or> s = 3 then 4
        else if s = 4 then 3 
        else if s = 5 then 2
        else 0)"

fun end_stage :: "config \<Rightarrow> nat"
  where
    "end_stage (s, l, r) = 
          (if s = 2 \<or> s = 3 then (length r) else 0)"

fun end_step :: "config \<Rightarrow> nat"
  where
    "end_step (s, l, r) = 
         (if s = 4 then (if hd r = Oc then 1 else 0)
          else if s = 5 then length l
          else if s = 2 then 1
          else if s = 3 then 0
          else 0)"

definition end_LE :: "(config \<times> config) set"
  where
    "end_LE = measures [end_state, end_stage, end_step]"

lemma wf_end_le: "wf end_LE"
  unfolding end_LE_def by auto

lemma end_halt: 
  "\<lbrakk>x > 0; inv_end x (Suc 0, l, r)\<rbrakk> \<Longrightarrow> 
      \<exists> stp. is_final (steps (Suc 0, l, r) (tm_copy_end_new, 0) stp)"
proof(rule halt_lemma[OF wf_end_le])
  assume great: "0 < x"
    and inv_start: "inv_end x (Suc 0, l, r)"
  show "\<forall>n. \<not> is_final (steps (Suc 0, l, r) (tm_copy_end_new, 0) n) \<longrightarrow> 
    (steps (Suc 0, l, r) (tm_copy_end_new, 0) (Suc n), steps (Suc 0, l, r) (tm_copy_end_new, 0) n) \<in> end_LE"
  proof(rule_tac allI, rule_tac impI)
    fix n
    assume notfinal: "\<not> is_final (steps (Suc 0, l, r) (tm_copy_end_new, 0) n)"
    obtain s' l' r' where d: "steps (Suc 0, l, r) (tm_copy_end_new, 0) n = (s', l', r')"
      apply(case_tac "steps (Suc 0, l, r) (tm_copy_end_new, 0) n", auto)
      done
    hence "inv_end x (s', l', r') \<and> s' \<noteq> 0"
      using great inv_start notfinal
      apply(drule_tac stp = n in inv_end_steps, auto)
      done
    hence "(step (s', l', r') (tm_copy_end_new, 0), s', l', r') \<in> end_LE"
      apply(cases r'; cases "hd r'")
         apply(auto simp: inv_end.simps step.simps tm_copy_end_new_def numeral_eqs_upto_12 end_LE_def split: if_splits)
      done
    thus "(steps (Suc 0, l, r) (tm_copy_end_new, 0) (Suc n), 
      steps (Suc 0, l, r) (tm_copy_end_new, 0) n) \<in> end_LE"
      using d
      by simp
  qed
qed

lemma end_correct:
  "n > 0 \<Longrightarrow> \<lbrace>inv_end1 n\<rbrace> tm_copy_end_new \<lbrace>inv_end0 n\<rbrace>"
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n"
    "inv_end1 n (l, r)"
  then have "\<exists> stp. is_final (steps0 (1, l, r) tm_copy_end_new stp)"
    by (simp add: end_halt inv_end.simps)
  then obtain stp where "is_final (steps0 (1, l, r) tm_copy_end_new stp)" ..
  moreover have "inv_end n (steps0 (1, l, r) tm_copy_end_new stp)"
    apply(rule_tac inv_end_steps)
    using h by(simp_all add: inv_end.simps)
  ultimately show
    "\<exists>stp. is_final (steps (1, l, r) (tm_copy_end_new, 0) stp) \<and> 
    inv_end0 n holds_for steps (1, l, r) (tm_copy_end_new, 0) stp"        
    using h
    apply(rule_tac x = stp in exI)
    apply(cases "(steps0 (1, l, r) tm_copy_end_new stp)") 
    apply(simp add: inv_end.simps)
    done
qed

(* ---------- tm_weak_copy ---------------------------------------- *)
(* This is the original weak variant, with a slightly modified end *)
(* --------------------------------------------------------------- *)

definition 
  tm_weak_copy :: "instr list"
  where
    "tm_weak_copy \<equiv> (tm_copy_begin_orig |+| tm_copy_loop_orig) |+| tm_copy_end_new"

(* The tm_weak_copy machine and all of its parts are composable
 * (in the old terminologies: well-formed)
 *)

lemma [intro]:
  "composable_tm (tm_copy_begin_orig, 0)"
  "composable_tm (tm_copy_loop_orig, 0)"
  "composable_tm (tm_copy_end_new, 0)"
  by (auto simp: composable_tm.simps tm_copy_end_new_def tm_copy_loop_orig_def tm_copy_begin_orig_def)

lemma composable_tm0_tm_weak_copy[intro, simp]: "composable_tm0 tm_weak_copy"
  by (auto simp: tm_weak_copy_def)

lemma tm_weak_copy_correct_pre: 
  assumes "0 < x"
  shows "\<lbrace>inv_begin1 x\<rbrace> tm_weak_copy \<lbrace>inv_end0 x\<rbrace>"
proof -
  have "\<lbrace>inv_begin1 x\<rbrace> tm_copy_begin_orig \<lbrace>inv_begin0 x\<rbrace>"
    by (metis assms begin_correct) 
  moreover 
  have "inv_begin0 x \<mapsto> inv_loop1 x"
    unfolding assert_imp_def
    unfolding inv_begin0.simps inv_loop1.simps
    unfolding inv_loop1_loop.simps inv_loop1_exit.simps
    apply(auto simp add: numeral_eqs_upto_12 Cons_eq_append_conv)
    by (rule_tac x = "Suc 0" in exI, auto)
  ultimately have "\<lbrace>inv_begin1 x\<rbrace> tm_copy_begin_orig \<lbrace>inv_loop1 x\<rbrace>"
    by (rule_tac Hoare_consequence) (auto)
  moreover
  have "\<lbrace>inv_loop1 x\<rbrace> tm_copy_loop_orig \<lbrace>inv_loop0 x\<rbrace>"
    by (metis assms loop_correct) 
  ultimately 
  have "\<lbrace>inv_begin1 x\<rbrace> (tm_copy_begin_orig |+| tm_copy_loop_orig) \<lbrace>inv_loop0 x\<rbrace>"
    by (rule_tac Hoare_plus_halt) (auto)
  moreover 
  have "\<lbrace>inv_end1 x\<rbrace> tm_copy_end_new \<lbrace>inv_end0 x\<rbrace>"
    by (metis assms end_correct) 
  moreover 
  have "inv_loop0 x = inv_end1 x"
    by(auto simp: inv_end1.simps inv_loop1.simps assert_imp_def)
  ultimately 
  show "\<lbrace>inv_begin1 x\<rbrace> tm_weak_copy \<lbrace>inv_end0 x\<rbrace>"
    unfolding tm_weak_copy_def
    by (rule_tac Hoare_plus_halt) (auto)
qed

lemma tm_weak_copy_correct:
  shows "\<lbrace>\<lambda>tap. tap = ([]::cell list, Oc \<up> (Suc n))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap= ([Bk], <(n, n::nat)>)\<rbrace>"
proof -
  have "\<lbrace>inv_begin1 (Suc n)\<rbrace> tm_weak_copy \<lbrace>inv_end0 (Suc n)\<rbrace>"
    by (rule tm_weak_copy_correct_pre) (simp)
  moreover
  have "(\<lambda>tap. tap = ([]::cell list, Oc \<up> (Suc n))) = inv_begin1 (Suc n)"
    by (auto)
  moreover
  have "inv_end0 (Suc n) = (\<lambda>tap. tap= ([Bk], <(n, n::nat)>))"
    unfolding fun_eq_iff
    by (auto simp add: inv_end0.simps tape_of_nat_def tape_of_prod_def)
  ultimately
  show "\<lbrace>\<lambda>tap. tap = ([]::cell list, Oc \<up> (Suc n))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap= ([Bk], <(n, n::nat)>)\<rbrace>" 
    by simp
qed

(* additional variants of tm_weak_copy_correct *)

lemma tm_weak_copy_correct5: "\<lbrace>\<lambda>tap. tap = ([], <[n::nat]>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[n, n]> @ Bk \<up> l) \<rbrace>"
proof -
  have "\<lbrace>\<lambda>tap. tap = ([], <n::nat>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>"
    using tape_of_list_def tape_of_nat_def tape_of_nat_list.simps(2) tm_weak_copy_correct by auto
  then have "\<lbrace>\<lambda>tap. tap = ([], <n::nat>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk], <[n, n]>)\<rbrace>"
  proof -
    assume "\<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>"
    moreover have  "<(n, n)> = <[n, n]>"
      by (simp add:   tape_of_list_def tape_of_nat_list.elims tape_of_prod_def)
    ultimately show ?thesis
      by auto
  qed
  then have "\<lbrace>\<lambda>tap. tap = ([], <[n::nat]>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk], <[n, n]>)\<rbrace>"
    by (metis tape_of_list_def tape_of_nat_list.simps(2))
  then show ?thesis
    by (smt Hoare_haltE Hoare_haltI One_nat_def append.right_neutral
            holds_for.elims(2) holds_for.simps replicate.simps(1) replicate.simps(2))
qed

lemma tm_weak_copy_correct6:
  "\<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <[n::nat]> @[Bk])\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[n::nat, n]> @ Bk \<up> l) \<rbrace>" 
proof -
  have "\<lbrace>\<lambda>tap. tap = ([], <[n::nat]>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[n::nat, n]> @ Bk \<up> l) \<rbrace>"
    by (rule tm_weak_copy_correct5)
  then have "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, <[n::nat]> @ Bk \<up> ll)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <[n::nat, n]> @ Bk \<up> lr)\<rbrace>"
    using TMC_has_num_res_list_without_initial_Bks_imp_TMC_has_num_res_list_after_adding_Bks_to_initial_left_and_right_tape by auto
  then have "\<lbrace>\<lambda>tap. \<exists>z4. tap = (Bk \<up> z4, <[n::nat]> @ Bk \<up> (Suc 0))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <[n::nat, n]> @ Bk \<up> lr)\<rbrace>"
    by (smt Hoare_haltE Hoare_haltI)
  then show ?thesis
    by auto
qed

(* ---------------------------------------------------- *)
(* Properties of tm_weak_copy for lists of length \<noteq> 1   *)
(* ---------------------------------------------------- *)

(* FABR: Some principle reminder about rewriting/simplification of properties for composed TMs
 *  value "steps0 (1, [Bk,Bk], [Bk]) tm_weak_copy 3"
 *  > "(0, [Bk, Bk, Bk, Bk], [])"
 *
 *  value "steps0 (1, [Bk,Bk], [Bk]) tm_weak_copy 3 = (0, [Bk, Bk, Bk, Bk], [])"
 *  > True
 *
 * 1) If we define a TM directly by an instruction list, the simplifier is able
 *    to compute results (as is the 'value' instruction).
 *
 * 2) However, if we define TMs by seq_tm, we must add more rules for rewriting
 *
 * Examples:
 *
 * Machine tm_strong_copy_post is identical to tm_weak_copy
 * However,
 *  tm_strong_copy_post is defined as a plain instruction list
 *  tm_weak_copy is defined by seqeuntial composition
 *
 *  "tm_weak_copy \<equiv> (tm_copy_begin_orig |+| tm_copy_loop_orig) |+| tm_copy_end_new"
 *
 *)

definition 
  strong_copy_post :: "instr list"
  where
    "strong_copy_post \<equiv> [
       (WB,5),(R,2), (R,3),(R,2),    (WO,3),(L,4),  (L,4),(L,5),    (R,11),(R,6),
       (R,7),(WB,6), (R,7),(R,8),    (WO,9),(R,8),  (L,10),(L,9),   (L,10),(L,5),
       (R,0),(R,12), (WO,13),(L,14), (R,12),(R,12), (L,15),(WB,14), (R,0),(L,15)
     ]"

value "steps0 (1, [Bk,Bk], [Bk]) strong_copy_post 3 = (0::nat, [Bk, Bk, Bk, Bk], [])"

lemma "steps0 (1, [Bk,Bk], [Bk]) strong_copy_post 3 = (0::nat, [Bk, Bk, Bk, Bk], [])"
  by (simp add: step.simps steps.simps numeral_eqs_upto_12  strong_copy_post_def)

(* now, we try the same proof for tm_weak_copy *)

(* The rewriter is not able to solve the problem like this:

lemma "steps0 (1, [Bk,Bk], [Bk]) tm_weak_copy 3 = (0::nat, [Bk, Bk, Bk, Bk], [])"
  by (simp add: step.simps steps.simps numeral_eqs_upto_12
                tm_weak_copy_def strong_copy_post_def
                tm_copy_begin_orig_def tm_copy_loop_orig_def tm_copy_end_new_def
                adjust.simps shift.simps seq_tm.simps)
*)

(* There are at least the following two solutions: *)

(* Solution 1:
 *   Prove equality "tm_weak_copy = strong_copy_post"
 *   and rewrite with respect to plain instruction list strong_copy_post
 *)

lemma tm_weak_copy_eq_strong_copy_post: "tm_weak_copy = strong_copy_post"
  unfolding tm_weak_copy_def strong_copy_post_def
            tm_copy_begin_orig_def tm_copy_loop_orig_def tm_copy_end_new_def
  by (simp add: adjust.simps shift.simps seq_tm.simps)

lemma tm_weak_copy_correct11:
  "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
proof -
  have "steps0 (1, [Bk,Bk], [Bk]) strong_copy_post 3 = (0::nat, [Bk, Bk, Bk, Bk], [])"
    by (simp add: step.simps steps.simps numeral_eqs_upto_12  strong_copy_post_def)
  then show ?thesis
    by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
qed

lemma tm_weak_copy_correct12: (* this lemma is not used anywhere *)
  "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = ( Bk \<up> k, Bk \<up> l) \<rbrace>"
proof -
  have "Bk \<up> 4 = [Bk, Bk, Bk, Bk]"
    by (simp add: numeral_eqs_upto_12)
  moreover have "Bk \<up> 0 = []"
    by (simp add: numeral_eqs_upto_12)
  ultimately
  have "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ( Bk \<up> 4, Bk \<up> 0) \<rbrace>"
    using tm_weak_copy_correct11
    by auto
  then show ?thesis
    by (metis (no_types, lifting)  Hoare_halt_def holds_for.elims(2) holds_for.simps)
qed

lemma tm_weak_copy_correct13:
  "\<lbrace>\<lambda>tap. tap = ([], [Bk,Bk]@r) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk], r) \<rbrace>" 
proof -
  have "steps0 (1, [], [Bk,Bk]@r) strong_copy_post 3 = (0::nat, [Bk,Bk], r)"
    by (simp add: step.simps steps.simps numeral_eqs_upto_12  strong_copy_post_def)
  then show ?thesis
    by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
qed

(* Solution 2: (pays off for more complicated cases)
 *
 *   Use compositional reasoning on components of tm_weak_copy using our Hoare rules."
 *
 *   "tm_weak_copy \<equiv> (tm_copy_begin_orig |+| tm_copy_loop_orig) |+| tm_copy_end_new"
 *
 * See our exploration in file HaskellCode/EngineeringOf_StrongCopy.hs
 * These yield the concrete steps and results to compute for the intermediate
 * steps in the following proofs.
 *
 *)

(* A compositional proof using Hoare_rules for
 *
 *    "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
 *
 * "steps0 (1, [Bk, Bk],     [Bk]) tm_copy_begin_orig 1 = (0, [Bk, Bk],         [Bk])"
 * "steps0 (1, [Bk, Bk],     [Bk]) tm_copy_loop_orig  1 = (0, [Bk, Bk, Bk],     []  )"
 * "steps0 (1, [Bk, Bk, Bk], []  ) tm_copy_end_new    1 = (0, [Bk, Bk, Bk, Bk], []  )"
 *
 * See HaskellCode/EngineeringOf_StrongCopy.hs for the exploration.
 *)

lemma tm_weak_copy_correct11':
  "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
proof -
  have "\<lbrace>\<lambda>tap. tap = ([Bk,Bk], [Bk]) \<rbrace>
        (tm_copy_begin_orig |+| tm_copy_loop_orig) |+| tm_copy_end_new
        \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 (tm_copy_begin_orig |+| tm_copy_loop_orig)"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_copy_begin_orig_def tm_copy_loop_orig_def)
  next
    show "\<lbrace>\<lambda>tap. tap = ([Bk, Bk, Bk], [])\<rbrace> tm_copy_end_new \<lbrace>\<lambda>tap. tap = ([Bk, Bk, Bk, Bk], [])\<rbrace>"
    proof -
      have "steps0 (1, [Bk, Bk, Bk], []) tm_copy_end_new 1 = (0, [Bk, Bk, Bk, Bk], [])"
        by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_end_new_def)
      then show ?thesis
        by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
    qed
  next
    show " \<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace>
           tm_copy_begin_orig |+| tm_copy_loop_orig
           \<lbrace>\<lambda>tap. tap = ([Bk, Bk, Bk], [])\<rbrace>"
    proof (rule Hoare_plus_halt)
      show "composable_tm0 tm_copy_begin_orig"
        by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
            tm_copy_begin_orig_def)
    next
      show "\<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace> tm_copy_begin_orig \<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace>"
      proof -
        have "steps0 (1, [Bk, Bk], [Bk]) tm_copy_begin_orig 1 = (0, [Bk, Bk], [Bk])"
          by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_begin_orig_def)
        then show ?thesis
          by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
      qed
    next
      show "\<lbrace>\<lambda>tap. tap = ([Bk, Bk], [Bk])\<rbrace> tm_copy_loop_orig \<lbrace>\<lambda>tap. tap = ([Bk, Bk, Bk], [])\<rbrace>"
      proof -
        have "steps0 (1, [Bk, Bk], [Bk]) tm_copy_loop_orig 1 = (0, [Bk, Bk, Bk], [])"
          by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_loop_orig_def)
        then show ?thesis
          by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
      qed
    qed
  qed
  then show ?thesis
    unfolding tm_weak_copy_def
    by auto
qed

(* -- *)

(* A compositional proof using Hoare_rules for
 *
 *    "\<lbrace>\<lambda>tap. tap = ([], [Bk,Bk]@r) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = ([Bk,Bk], r) \<rbrace>"
 *
 * "steps0 (1, [],   [Bk,Bk] @ r) tm_copy_begin_orig 1 = (0, [],       [Bk,Bk] @ r)"
 * "steps0 (1, [],   [Bk,Bk] @ r) tm_copy_loop_orig  1 = (0, [Bk],     [Bk]    @ r)"
 * "steps0 (1, [Bk], [Bk]    @ r) tm_copy_end_new    1 = (0, [Bk, Bk],           r)"
 *
 * See HaskellCode/EngineeringOf_StrongCopy.hs for the exploration.
 *)

lemma tm_weak_copy_correct13':
  "\<lbrace>\<lambda>tap. tap = ([], [Bk,Bk]@r) \<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk], r) \<rbrace>" 
proof -
  have "\<lbrace>\<lambda>tap. tap = ([], [Bk,Bk]@r) \<rbrace>
        (tm_copy_begin_orig |+| tm_copy_loop_orig) |+| tm_copy_end_new
        \<lbrace>\<lambda>tap. tap = ([Bk,Bk], r) \<rbrace>"
  proof (rule Hoare_plus_halt)
    show "composable_tm0 (tm_copy_begin_orig |+| tm_copy_loop_orig)"
      by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
          tm_copy_begin_orig_def tm_copy_loop_orig_def)
  next
    show "\<lbrace>\<lambda>tap. tap = ([Bk], [Bk] @ r)\<rbrace> tm_copy_end_new \<lbrace>\<lambda>tap. tap = ([Bk, Bk], r)\<rbrace>"
    proof -
      have "steps0 (1, [Bk], [Bk]  @ r) tm_copy_end_new 1 = (0, [Bk, Bk], r)"
        by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_end_new_def)
      then show ?thesis
        by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
    qed
  next
    show " \<lbrace>\<lambda>tap. tap = ([], [Bk, Bk] @ r)\<rbrace>
           tm_copy_begin_orig |+| tm_copy_loop_orig
           \<lbrace>\<lambda>tap. tap = ([Bk], [Bk] @ r)\<rbrace>"
    proof (rule Hoare_plus_halt)
      show "composable_tm0 tm_copy_begin_orig"
        by (simp add: composable_tm.simps adjust.simps shift.simps seq_tm.simps 
            tm_copy_begin_orig_def)
    next
      show "\<lbrace>\<lambda>tap. tap = ([], [Bk, Bk] @ r)\<rbrace> tm_copy_begin_orig \<lbrace>\<lambda>tap. tap = ([], [Bk,Bk] @ r)\<rbrace>"
      proof -
        have "steps0 (1, [], [Bk, Bk] @ r) tm_copy_begin_orig 1 = (0, [], [Bk,Bk] @ r)"
          by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_begin_orig_def)
        then show ?thesis
          by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
      qed
    next
      show "\<lbrace>\<lambda>tap. tap = ([], [Bk, Bk] @ r)\<rbrace> tm_copy_loop_orig \<lbrace>\<lambda>tap. tap = ([Bk], [Bk] @ r)\<rbrace>"
      proof -
        have "steps0 (1, [], [Bk,Bk] @ r) tm_copy_loop_orig 1 = (0, [Bk], [Bk] @ r)"
          by (simp add: step.simps steps.simps numeral_eqs_upto_12  tm_copy_loop_orig_def)
        then show ?thesis
          by (smt Hoare_haltI holds_for.simps is_final_eq tm_weak_copy_eq_strong_copy_post)
      qed
    qed
  qed
  then show ?thesis
    unfolding tm_weak_copy_def
    by auto
qed

end
