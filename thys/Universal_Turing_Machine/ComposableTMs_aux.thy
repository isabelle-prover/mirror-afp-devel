(* Title: thys/ComposableTMs_aux.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

theory ComposableTMs_aux
  imports ComposableTMs
begin

(* --------------------------------------------------- *)
(* Exhaustion-/Case-Lemmas for actions and instr lists *)
(* Currently none of these lemmas is in use            *)
(* --------------------------------------------------- *)

lemma nat_cases_0_1_gt1 (* [case_names Zero One GtOne, cases type: nat] *) :
  assumes "(n::nat) = (0::nat) \<Longrightarrow> P"
    and "(n::nat) = (1::nat) \<Longrightarrow> P"
    and "2 \<le> (n::nat) \<Longrightarrow> P"
  shows P
proof -
  have "n= 0 \<or> n = 1 \<or> (\<exists>m. n = Suc (Suc m))"
    by (induct n) auto
  with assms  show P by auto
qed

lemma list_len_1_is_singleton: "length l = 1 \<Longrightarrow> (\<exists>x. l = [x])"
  by (induct l) auto

lemma action_exhaust2: "actn = WB \<or> actn = WO \<or> actn = L \<or> actn = R \<or> actn = Nop"
  by (rule Turing.action.exhaust) auto

lemma instr_exhaust: "\<exists>nxt. ins = (WB, nxt)  \<or> ins = (WO, nxt) \<or> ins = (L, nxt) \<or> ins = (R, nxt) \<or> ins = (Nop, nxt)"
proof (cases ins)
  case (Pair a b)
  then have "ins = (a, b)" .
  show ?thesis
  proof (rule Turing.action.exhaust)
    assume "a = WB"
    with \<open>ins = (a, b)\<close> have "ins = (WB, b) \<or> ins = (WO, b) \<or> ins = (L, b) \<or> ins = (R, b) \<or> ins = (Nop, b)" by auto
    then show ?thesis by auto
  next
    assume "a = WO"
    with \<open>ins = (a, b)\<close> have "ins = (WB, b) \<or> ins = (WO, b) \<or> ins = (L, b) \<or> ins = (R, b) \<or> ins = (Nop, b)" by auto
    then show ?thesis by auto
  next
    assume "a = L"
    with \<open>ins = (a, b)\<close> have "ins = (WB, b) \<or> ins = (WO, b) \<or> ins = (L, b) \<or> ins = (R, b) \<or> ins = (Nop, b)" by auto
    then show ?thesis by auto
  next
    assume "a = R"
    with \<open>ins = (a, b)\<close> have "ins = (WB, b) \<or> ins = (WO, b) \<or> ins = (L, b) \<or> ins = (R, b) \<or> ins = (Nop, b)" by auto
    then show ?thesis by auto
  next
    assume "a = Nop"
    with \<open>ins = (a, b)\<close> have "ins = (WB, b) \<or> ins = (WO, b) \<or> ins = (L, b) \<or> ins = (R, b) \<or> ins = (Nop, b)" by auto
    then show ?thesis by auto
  qed
qed

(* Attention:
    Secifiying  instr_cases  [case_names WB WO L R Nop, cases type: nat] :
    breaks proofs
      seq_tm_exec_after_first
    in Turingomp.thy 
*)
lemma instr_cases (* [case_names WB WO L R Nop, cases type: nat] *) :
  assumes "\<And>nxt. ins = (WB, nxt) \<Longrightarrow> P"
    and "\<And>nxt. ins = (WO, nxt) \<Longrightarrow> P"
    and "\<And>nxt. ins = (L, nxt) \<Longrightarrow> P"
    and "\<And>nxt. ins = (R, nxt) \<Longrightarrow> P"
    and "\<And>nxt. ins = (Nop, nxt) \<Longrightarrow> P"
  shows P
proof -
  have "\<exists>nxt. ins = (WB, nxt)  \<or> ins = (WO, nxt) \<or> ins = (L, nxt) \<or> ins = (R, nxt) \<or> ins = (Nop, nxt)"
    by (rule instr_exhaust)
  then obtain nxt where w_nxt: "ins = (WB, nxt)  \<or> ins = (WO, nxt) \<or> ins = (L, nxt) \<or> ins = (R, nxt) \<or> ins = (Nop, nxt)" by blast
  with assms show P by auto
qed

lemma sigleton_tm_exhaust: "length (tm::instr list) = 1 \<Longrightarrow> \<exists>nxt. tm = [(WB, nxt)]  \<or> tm = [(WO, nxt)] \<or> tm = [(L, nxt)] \<or> tm = [(R, nxt)] \<or> tm = [(Nop, nxt)]"
proof -
  assume "length (tm::instr list) = 1"
  then have "(\<exists>instr. tm = [instr])" by (rule list_len_1_is_singleton)
  then obtain instr where w_instr: "tm = [instr]" by blast
  have "\<exists>nxt. instr = (WB, nxt) \<or> instr = (WO, nxt) \<or> instr = (L, nxt) \<or> instr = (R, nxt) \<or> instr = (Nop, nxt)" by (rule instr_exhaust)
  then obtain nxt where w_nxt: "instr = (WB, nxt) \<or> instr = (WO, nxt) \<or> instr = (L, nxt) \<or> instr = (R, nxt) \<or> instr = (Nop, nxt)" by blast
  with w_instr show ?thesis by auto
qed

lemma split_action_all: "(\<forall>nxt. P nxt) \<longleftrightarrow> (\<forall>nxt. P (WB, nxt)) \<and> (\<forall>nxt. P (WO, nxt)) \<and> (\<forall>nxt. P (L, nxt)) \<and> (\<forall>nxt. P (R, nxt)) \<and> (\<forall>nxt. P (Nop, nxt))"
  by (auto intro: action.induct)

(* Attention:
    Secifiying  tm_instr_cases [consumes 1, case_names WB WO L R Nop, cases type: nat] :
    breaks proofs
      modify_tprog_fetch_odd
    in UF.thy 
*)
lemma tm_instr_cases (* [consumes 1, case_names WB WO L R Nop, cases type: nat] *):
  assumes  "length (tm::instr list) = 1"
    and "\<And>nxt. tm = [(WB, nxt)] \<Longrightarrow> P"
    and "\<And>nxt. tm = [(WO, nxt)] \<Longrightarrow> P"
    and "\<And>nxt. tm = [(L, nxt)] \<Longrightarrow> P"
    and "\<And>nxt. tm = [(R, nxt)] \<Longrightarrow> P"
    and "\<And>nxt. tm = [(Nop, nxt)] \<Longrightarrow> P"
  shows P
proof -
  from \<open>length tm = 1\<close> have "\<exists>nxt. tm = [(WB, nxt)]  \<or> tm = [(WO, nxt)] \<or> tm = [(L, nxt)] \<or> tm = [(R, nxt)] \<or> tm = [(Nop, nxt)]"
    by (rule sigleton_tm_exhaust)
  then obtain nxt where w_nxt: "tm = [(WB, nxt)]  \<or> tm = [(WO, nxt)] \<or> tm = [(L, nxt)] \<or> tm = [(R, nxt)] \<or> tm = [(Nop, nxt)]" by blast
  with assms show P by auto
qed

end
