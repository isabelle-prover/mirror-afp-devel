(*  Title:       Isabelle/Circus
    Author:      Abderrahmane Feliachi, Burkhart Wolff, Marie-Claude Gaudel
                 Univ. Paris-Sud / LRI
    Maintainer:  Abderrahmane Feliachi
*)

theory Reactive_Processes
imports Designs
begin

subsection{* Reactive Processes \label{sec:UTP_Reactive_Processes} *}
text{*\label{Reactive_Processes}*}
text {* Following the technique already used to repesent termination by 
the observational variable \inlineisar+ok+, the UTP 
 describes reactive processes by introducing more observational
variables are needed to record the interaction with the environment. Three observational 
variables are defined for this subset of relations: $wait$, $tr$ and $ref$.
The boolean variable $wait$ records if the process is waiting for an interaction
or has terminated. $tr$ records the list (trace) of interactions the process has
performed so far. The variable $ref$ contains the set of interactions (events) the
process may refuse to perform. *}



text {* In this subsection, we introduce first some preliminary notions, useful for 
 trace manipulations. The definitions of reactive process alphabets and healthiness 
conditions are also given. Finally, proved lemmas and theorems are listed.*}

subsubsection {* Preliminaries *}

type_synonym '\<alpha> trace = "'\<alpha> list"

fun list_diff::"'\<alpha> list \<Rightarrow> '\<alpha> list \<Rightarrow> '\<alpha> list option" where
    "list_diff [] [] = Some []"
  | "list_diff [] l = None"
  | "list_diff l [] = Some l"
  | "list_diff (x#xs) (y#ys) = (if (x = y) then (list_diff xs ys) else None)"

instantiation  list :: (type) minus
begin
definition list_minus : "l1 - l2 \<equiv> the (list_diff l1 l2)"
instance ..
end

lemma list_diff_empty [simp]: "the (list_diff l []) = l"
by (cases l) auto

lemma prefix_diff_empty [simp]: "l  - [] = l"
by (induct l) (auto simp: list_minus)
 
lemma prefix_diff_eq [simp]: "l - l = []"
by (induct l) (auto simp: list_minus)

lemma prefix_diff [simp]: "(l @ t) - l = t"
by (induct l) (auto simp: list_minus)

lemma prefix_subst [simp]: "l @ t = m \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_subst1 [simp]: "m = l @ t \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_diff1 [simp]: "((l @ m) @ t) - (l @ m) = t"
by (rule prefix_diff)

lemma prefix_diff2 [simp]: "(l @ (m @ t)) - (l @ m) = t"
apply (simp only: append_assoc [symmetric])
apply (rule prefix_diff1)
done

class ev_eq = fixes ev_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition "filter_chan_set a cs = (\<not> (\<exists> e\<in>cs. ev_eq a e))"
fun tr_filter::"'a::ev_eq list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
    "tr_filter [] cs = []"
  | "tr_filter (x#xs) cs = (if (filter_chan_set x cs) then (x#(tr_filter xs cs))
                                                                  else (tr_filter xs cs))"

instantiation list :: (ev_eq) ev_eq
begin
fun ev_eq_list where
    "ev_eq_list [] [] = True"
  | "ev_eq_list l [] = False"
  | "ev_eq_list [] l = False"
  | "ev_eq_list (x#xs) (y#ys) = (if (ev_eq x y) then (ev_eq_list xs ys) else False)"
instance ..
end

subsubsection {* Definitions *}

text {* The definitions of reactive process alphabets and healthiness conditions are given
in the following. The basic step is that the observational variables 
\inlineisar+wait+, \inlineisar+tr+ and \inlineisar+ref+ are included into the basic 
alphabet of all reactive processes  called ``\inlineisar+alpha_rp+''. *}


type_synonym '\<theta> refusal = "'\<theta> set"

  
record '\<theta> alpha_rp  = alpha_d + 
                         wait:: bool
                         tr  :: "'\<theta> trace"
                         ref :: "'\<theta> refusal"

text{* Note that we define here the class of UTP alphabets that contain
$wait$, $tr$ and $ref$, or, in other words, we define here the class of reactive process
alphabets. *}

type_synonym ('\<theta>,'\<sigma>) alphabet_rp  = "('\<theta>,'\<sigma>) alpha_rp_scheme alphabet"
type_synonym ('\<theta>,'\<sigma>) relation_rp  = "('\<theta>,'\<sigma>) alphabet_rp relation"

definition "diff_tr s1 s2 = ((tr s1) - (tr s2))"

definition spec :: "[bool, bool, ('\<theta>,'\<sigma>) relation_rp] \<Rightarrow> ('\<theta>,'\<sigma>) relation_rp"
where "spec b b' P \<equiv> \<lambda> (A, A'). P (A\<lparr>wait := b'\<rparr>, A'\<lparr>ok := b\<rparr>)"

abbreviation Speciftt ("_\<^sup>t\<^sub>t") where "(P)\<^sup>t\<^sub>t \<equiv> spec True True P"

abbreviation Specifff ("_\<^sup>f\<^sub>f") where "(P)\<^sup>f\<^sub>f \<equiv> spec False False P"

abbreviation Speciftf ("_\<^sup>t\<^sub>f") where "(P)\<^sup>t\<^sub>f \<equiv> spec True False P"

abbreviation Specifft ("_\<^sup>f\<^sub>t") where "(P)\<^sup>f\<^sub>t \<equiv> spec False True P"


text{* Particular invariants on reactive designs must be introduce
in order to exclude non-interpretable processes. These invariants
were traditionally called " healthiness conditions" of reactive processes 
and are defined by  $R1$, $R2$, $R3$ and their composition $R$.*}

text{*
Some healthiness conditions are defined over \inlineisar+wait+, 
\inlineisar+tr+ and \inlineisar+ref+ to ensure that a recative process 
satisfies some properties \cite{CW06}. *}


definition R1::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R1 (P)  \<equiv>  \<lambda>(A, A'). (P (A, A')) \<and> prefixeq (tr A) (tr A')"

definition R2::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R2 (P)  \<equiv> \<lambda>(A, A'). (P (A\<lparr>tr:=[]\<rparr>,A'\<lparr>tr:= tr A' - tr A\<rparr>) \<and> prefixeq (tr A) (tr A'))"

definition \<Pi>rea   
where "\<Pi>rea  \<equiv> \<lambda>(A, A'). (\<not>ok A \<and> prefixeq (tr A) (tr A')) \<or> (ok A' \<and> tr A = tr A' 
                            \<and> (wait A = wait A') \<and> ref A = ref A' \<and> more A = more A')"

definition R3::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R3 (P)  \<equiv> (\<Pi>rea \<triangleleft> wait o fst \<triangleright> P)"

definition R::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition" 
where "R  \<equiv> R3 o R2 o R1"

lemmas rp_defs = R1_def R2_def \<Pi>rea_def R3_def R_def spec_def

subsubsection {* Proofs *}

lemma tr_filter_empty [simp]: "tr_filter l {} = l"
by (induct l) (auto simp: filter_chan_set_def)

lemma trf_imp_filtercs: "\<lbrakk>xs = tr_filter ys cs; xs \<noteq> []\<rbrakk> \<Longrightarrow> filter_chan_set (hd xs) cs"
apply (induct xs, auto)
apply (induct ys, auto)
apply (case_tac "filter_chan_set a cs", auto)
done

lemma filtercs_imp_trf: 
"\<lbrakk>filter_chan_set x cs; xs = tr_filter ys cs\<rbrakk> \<Longrightarrow> x#xs = tr_filter (x#ys) cs"
by (induct xs) auto

lemma alpha_d_more_eqI:
  assumes "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  shows "alpha_d.more r = alpha_d.more r'"
  using assms by (cases r, cases r') auto

lemma alpha_d_more_eqE:
  assumes "alpha_d.more r = alpha_d.more r'"
  obtains "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  using assms by (cases r, cases r') auto

lemma alpha_rp_eqE:
  assumes "r = r'"
  obtains "ok r = ok r'" "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  using assms by (cases r, cases r') auto

lemma R_idem: "R o R = R"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R_idem2: "R (R P) = R P"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R1_idem: "R1 o R1 = R1"
by (auto simp: rp_defs design_defs)

lemma R1_idem2: "R1 (R1 x) = R1 x"
by (auto simp: rp_defs design_defs)

lemma R2_idem: "R2 o R2 = R2"
by (auto simp: rp_defs design_defs)

lemma R2_idem2: "R2 (R2 x) = R2 x"
by (auto simp: rp_defs design_defs)

lemma R3_idem: "R3 o R3 = R3"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R3_idem2: "R3 (R3 x) = R3 x"
by (auto simp: R3_idem[simplified Fun.comp_def fun_eq_iff] fun_eq_iff)

lemma R1_R2_commute: "R1 o R2 = R2 o R1"
by (auto simp: rp_defs prefix_def design_defs fun_eq_iff)

lemma R1_R3_commute: "R1 o R3 = R3 o R1"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R2_R3_commute: "R2 o R3 = R3 o R2"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits elim: prefixeqE)

lemma R_abs_R1: "R o R1 = R"
apply (auto simp: R_def)
apply (subst R1_idem[symmetric]) back back
apply (auto)
done

lemma R_abs_R2: "R o R2 = R"
by (auto simp: rp_defs design_defs fun_eq_iff)

lemma R_abs_R3: "R o R3 = R"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits elim: prefixE)

lemma R_is_R1:
  assumes A: "P is R healthy"
  shows  "P is R1 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R1 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_is_R2:
  assumes A: "P is R healthy"
  shows  "P is R2 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R2 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff prefixeq_def split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_is_R3:
  assumes A: "P is R healthy"
  shows  "P is R3 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R3 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_disj:
  assumes A: "P is R healthy"
  assumes B: "Q is R healthy"
  shows  "(P \<or> Q) is R healthy"
proof -
  have "R P = P" and "R Q = Q"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R P) \<or> (R Q)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_disj2:  "R (P \<or> Q) = (R P \<or> R Q)"
apply (subst R_disj[simplified Healthy_def, where P="R P"])
apply (simp_all add: R_idem2)
apply (auto simp: fun_eq_iff rp_defs split: cond_splits)
done

lemma R1_comp:
  assumes "P is R1 healthy"
    and "Q is R1 healthy"
  shows "(P;;Q) is R1 healthy"
proof -
  have "R1 P = P" and "R1 Q = Q"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R1 P) ;; (R1 Q)) is R1 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R1_comp2:
  assumes A: "P is R1 healthy"
  assumes B: "Q is R1 healthy"
  shows  "R1 (P;;Q) = ((R1 P);;Q)"
using A B
apply (subst R1_comp[simplified Healthy_def, symmetric])
apply (auto simp: fun_eq_iff rp_defs design_defs)
done

lemma J_is_R1: "J is R1 healthy"
  by (auto simp: rp_defs design_defs fun_eq_iff elim: alpha_d_more_eqE)

lemma J_is_R2: "J is R2 healthy"
  by (auto simp: rp_defs design_defs fun_eq_iff prefixeq_def
    elim!: alpha_d_more_eqE intro!: alpha_d_more_eqI)

lemma R1_H2_commute2: "R1 (H2 P) = H2 (R1 P)"
  by (auto simp add: H2_def R1_def J_def fun_eq_iff
    elim!: alpha_d_more_eqE intro!: alpha_d_more_eqI)

lemma R1_H2_commute: "R1 o H2 = H2 o R1"
by (auto simp: R1_H2_commute2)

lemma R2_H2_commute2: "R2 (H2 P) = H2 (R2 P)"
apply (auto simp add: fun_eq_iff rp_defs design_defs prefixeq_def)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro)
apply (auto simp: fun_eq_iff prefixeq_def
  elim!: alpha_d_more_eqE alpha_rp_eqE intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro,
  auto simp: elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro,
  auto simp: elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
done

lemma R2_H2_commute: "R2 o H2 = H2 o R2"
by (auto simp: R2_H2_commute2)

lemma R3_H2_commute2: "R3 (H2 P) = H2 (R3 P)"
apply (auto simp: fun_eq_iff rp_defs design_defs prefixeq_def 
            elim: alpha_d_more_eqE split: cond_splits)
apply (rule_tac b="b" in comp_intro, auto split: cond_splits)
done

lemma R3_H2_commute: "R3 o H2 = H2 o R3"
by (auto simp: R3_H2_commute2)

lemma R_join: 
  assumes "x is R healthy"
  and "y is R healthy"
  shows "(x \<sqinter> y) is R healthy"
proof -
  have "R x = x" and "R y = y"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R x) \<sqinter> (R y)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_meet:
  assumes A: "x is R healthy"
  and B:"y is R healthy"
  shows "(x \<squnion> y) is R healthy"
proof -
  have "R x = x" and "R y = y"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R x) \<squnion> (R y)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed


lemma R_H2_commute: "R o H2 = H2 o R"
apply (auto simp add: rp_defs design_defs fun_eq_iff split: cond_splits 
                     elim: alpha_d_more_eqE)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro, auto split: cond_splits
  elim!: alpha_d_more_eqE alpha_rp_eqE intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac s=ba in subst, auto intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac s=ba in subst, auto intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro, auto split: cond_splits)
apply (rule_tac s=ba in subst,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality split: cond_splits)
apply (rule_tac s=ba in subst,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
done

lemma R_H2_commute2: "R (H2 P) = H2 (R P)"
by (auto simp: fun_eq_iff R_H2_commute[simplified fun_eq_iff Fun.comp_def])

end
