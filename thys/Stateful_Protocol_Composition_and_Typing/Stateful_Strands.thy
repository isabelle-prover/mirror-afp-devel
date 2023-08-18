(*  Title:      Stateful_Strands.thy
    Author:     Andreas Viktor Hess, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)


section \<open>Stateful Strands\<close>
theory Stateful_Strands
imports Strands_and_Constraints
begin

subsection \<open>Stateful Constraints\<close>
datatype (funs\<^sub>s\<^sub>s\<^sub>t\<^sub>p: 'a, vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p: 'b) stateful_strand_step = 
  Send (the_msgs: "('a,'b) term list") ("send\<langle>_\<rangle>" 80)
| Receive (the_msgs: "('a,'b) term list") ("receive\<langle>_\<rangle>" 80)
| Equality (the_check: poscheckvariant) (the_lhs: "('a,'b) term") (the_rhs: "('a,'b) term")
    ("\<langle>_: _ \<doteq> _\<rangle>" [80,80])
| Insert (the_elem_term: "('a,'b) term") (the_set_term: "('a,'b) term") ("insert\<langle>_,_\<rangle>" 80)
| Delete (the_elem_term: "('a,'b) term") (the_set_term: "('a,'b) term") ("delete\<langle>_,_\<rangle>" 80)
| InSet (the_check: poscheckvariant) (the_elem_term: "('a,'b) term") (the_set_term: "('a,'b) term")
    ("\<langle>_: _ \<in> _\<rangle>" [80,80])
| NegChecks (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p: "'b list")
    (the_eqs: "(('a,'b) term \<times> ('a,'b) term) list")
    (the_ins: "(('a,'b) term \<times> ('a,'b) term) list")
    ("\<forall>_\<langle>\<or>\<noteq>: _ \<or>\<notin>: _\<rangle>" [80,80])
where
  "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Send _) = []"
| "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Receive _) = []"
| "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Equality _ _ _) = []"
| "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert _ _) = []"
| "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete _ _) = []"
| "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ _ _) = []"

type_synonym ('a,'b) stateful_strand = "('a,'b) stateful_strand_step list"
type_synonym ('a,'b) dbstatelist = "(('a,'b) term \<times> ('a,'b) term) list"
type_synonym ('a,'b) dbstate = "(('a,'b) term \<times> ('a,'b) term) set"

abbreviation
  "is_Assignment x \<equiv> (is_Equality x \<or> is_InSet x) \<and> the_check x = Assign"

abbreviation
  "is_Check x \<equiv> ((is_Equality x \<or> is_InSet x) \<and> the_check x = Check) \<or> is_NegChecks x"

abbreviation
  "is_Check_or_Assignment x \<equiv> is_Equality x \<or> is_InSet x \<or> is_NegChecks x"

abbreviation
  "is_Update x \<equiv> is_Insert x \<or> is_Delete x"

abbreviation InSet_select ("select\<langle>_,_\<rangle>") where "select\<langle>t,s\<rangle> \<equiv> InSet Assign t s"
abbreviation InSet_check ("\<langle>_ in _\<rangle>") where "\<langle>t in s\<rangle> \<equiv> InSet Check t s"
abbreviation Equality_assign ("\<langle>_ := _\<rangle>") where "\<langle>t := s\<rangle> \<equiv> Equality Assign t s"
abbreviation Equality_check ("\<langle>_ == _\<rangle>") where "\<langle>t == s\<rangle> \<equiv> Equality Check t s"

abbreviation NegChecks_Inequality1 ("\<langle>_ != _\<rangle>") where
  "\<langle>t != s\<rangle> \<equiv> NegChecks [] [(t,s)] []"

abbreviation NegChecks_Inequality2 ("\<forall>_\<langle>_ != _\<rangle>") where
  "\<forall>x\<langle>t != s\<rangle> \<equiv> NegChecks [x] [(t,s)] []"

abbreviation NegChecks_Inequality3 ("\<forall>_,_\<langle>_ != _\<rangle>") where
  "\<forall>x,y\<langle>t != s\<rangle> \<equiv> NegChecks [x,y] [(t,s)] []"

abbreviation NegChecks_Inequality4 ("\<forall>_,_,_\<langle>_ != _\<rangle>") where
  "\<forall>x,y,z\<langle>t != s\<rangle> \<equiv> NegChecks [x,y,z] [(t,s)] []"

abbreviation NegChecks_NotInSet1 ("\<langle>_ not in _\<rangle>") where
  "\<langle>t not in s\<rangle> \<equiv> NegChecks [] [] [(t,s)]"

abbreviation NegChecks_NotInSet2 ("\<forall>_\<langle>_ not in _\<rangle>") where
  "\<forall>x\<langle>t not in s\<rangle> \<equiv> NegChecks [x] [] [(t,s)]"

abbreviation NegChecks_NotInSet3 ("\<forall>_,_\<langle>_ not in _\<rangle>") where
  "\<forall>x,y\<langle>t not in s\<rangle> \<equiv> NegChecks [x,y] [] [(t,s)]"

abbreviation NegChecks_NotInSet4 ("\<forall>_,_,_\<langle>_ not in _\<rangle>") where
  "\<forall>x,y,z\<langle>t not in s\<rangle> \<equiv> NegChecks [x,y,z] [] [(t,s)]"

fun trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Send ts) = set ts"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Receive ts) = set ts"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = {t,t'}"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert t t') = {t,t'}"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete t t') = {t,t'}"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ t t') = {t,t'}"
| "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks _ F F') = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F'"

definition trms\<^sub>s\<^sub>s\<^sub>t where "trms\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p ` set S)"
declare trms\<^sub>s\<^sub>s\<^sub>t_def[simp]

fun trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Send ts) = ts"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Receive ts) = ts"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = [t,t']"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert t t') = [t,t']"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete t t') = [t,t']"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ t t') = [t,t']"
| "trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks _ F F') = concat (map (\<lambda>(t,t'). [t,t']) (F@F'))"

definition trms_list\<^sub>s\<^sub>s\<^sub>t where "trms_list\<^sub>s\<^sub>s\<^sub>t S \<equiv> remdups (concat (map trms_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

definition ik\<^sub>s\<^sub>s\<^sub>t where "ik\<^sub>s\<^sub>s\<^sub>t A \<equiv> {t | t ts. Receive ts \<in> set A \<and> t \<in> set ts}"

definition bvars\<^sub>s\<^sub>s\<^sub>t::"('a,'b) stateful_strand \<Rightarrow> 'b set" where
  "bvars\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map (set \<circ> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p) S))"

fun fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p::"('a,'b) stateful_strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Send ts) = fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Receive ts) = fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = fv t \<union> fv t'"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert t t') = fv t \<union> fv t'"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete t t') = fv t \<union> fv t'"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ t t') = fv t \<union> fv t'"
| "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks X F F') = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' - set X"

definition fv\<^sub>s\<^sub>s\<^sub>t::"('a,'b) stateful_strand \<Rightarrow> 'b set" where
  "fv\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

fun fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle>) = concat (map fv_list ts)"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle>) = concat (map fv_list ts)"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>_: t \<doteq> s\<rangle>) = fv_list t@fv_list s"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle>) = fv_list t@fv_list s"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle>) = fv_list t@fv_list s"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>_: t \<in> s\<rangle>) = fv_list t@fv_list s"
| "fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>) = filter (\<lambda>x. x \<notin> set X) (fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@F'))"

definition fv_list\<^sub>s\<^sub>s\<^sub>t where
  "fv_list\<^sub>s\<^sub>s\<^sub>t S \<equiv> remdups (concat (map fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

declare bvars\<^sub>s\<^sub>s\<^sub>t_def[simp]
declare fv\<^sub>s\<^sub>s\<^sub>t_def[simp]

definition vars\<^sub>s\<^sub>s\<^sub>t::"('a,'b) stateful_strand \<Rightarrow> 'b set" where
  "vars\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

abbreviation wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p::"('a,'b) stateful_strand_step \<Rightarrow> 'b set" where
  "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<equiv>
    case x of
      NegChecks _ _ _ \<Rightarrow> {}
    | Equality Check _ _ \<Rightarrow> {}
    | InSet Check _ _ \<Rightarrow> {}
    | Delete _ _ \<Rightarrow> {}
    | _ \<Rightarrow> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x"

definition wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t::"('a,'b) stateful_strand \<Rightarrow> 'b set" where
  "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

abbreviation wfvarsoccs\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<equiv> 
    case x of
      Send ts \<Rightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set ts)
    | Equality Assign s t \<Rightarrow> fv s
    | InSet Assign s t \<Rightarrow> fv s \<union> fv t
    | _ \<Rightarrow> {}"

definition wfvarsoccs\<^sub>s\<^sub>s\<^sub>t where
  "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map wfvarsoccs\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"

fun wf'\<^sub>s\<^sub>s\<^sub>t::"'b set \<Rightarrow> ('a,'b) stateful_strand \<Rightarrow> bool" where
  "wf'\<^sub>s\<^sub>s\<^sub>t V [] = True"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Receive ts#S) = (fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> V \<and> wf'\<^sub>s\<^sub>s\<^sub>t V S)"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Send ts#S) = wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts)) S"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Equality Assign t t'#S) = (fv t' \<subseteq> V \<and> wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t) S)"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Equality Check _ _#S) = wf'\<^sub>s\<^sub>s\<^sub>t V S"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Insert t s#S) = (fv t \<subseteq> V \<and> fv s \<subseteq> V \<and> wf'\<^sub>s\<^sub>s\<^sub>t V S)"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (Delete _ _#S) = wf'\<^sub>s\<^sub>s\<^sub>t V S"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (InSet Assign t s#S) = wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv s) S"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (InSet Check _ _#S) = wf'\<^sub>s\<^sub>s\<^sub>t V S"
| "wf'\<^sub>s\<^sub>s\<^sub>t V (NegChecks _ _ _#S) = wf'\<^sub>s\<^sub>s\<^sub>t V S"

abbreviation "wf\<^sub>s\<^sub>s\<^sub>t S \<equiv> wf'\<^sub>s\<^sub>s\<^sub>t {} S \<and> fv\<^sub>s\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"

fun subst_apply_stateful_strand_step::
  "('a,'b) stateful_strand_step \<Rightarrow> ('a,'b) subst \<Rightarrow> ('a,'b) stateful_strand_step"
  (infix "\<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p" 51) where
  "send\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = send\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>"
| "receive\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>"
| "\<langle>a: t \<doteq> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<langle>a: (t \<cdot> \<theta>) \<doteq> (s \<cdot> \<theta>)\<rangle>"
| "\<langle>a: t \<in> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<langle>a: (t \<cdot> \<theta>) \<in> (s \<cdot> \<theta>)\<rangle>"
| "insert\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = insert\<langle>t \<cdot> \<theta>, s \<cdot> \<theta>\<rangle>"
| "delete\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = delete\<langle>t \<cdot> \<theta>, s \<cdot> \<theta>\<rangle>"
| "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>X\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<or>\<notin>: (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)\<rangle>"

definition subst_apply_stateful_strand::
  "('a,'b) stateful_strand \<Rightarrow> ('a,'b) subst \<Rightarrow> ('a,'b) stateful_strand"
  (infix "\<cdot>\<^sub>s\<^sub>s\<^sub>t" 51) where
  "S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) S"

fun dbupd\<^sub>s\<^sub>s\<^sub>t::"('f,'v) stateful_strand \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) dbstate \<Rightarrow> ('f,'v) dbstate"
where
  "dbupd\<^sub>s\<^sub>s\<^sub>t [] I D = D"
| "dbupd\<^sub>s\<^sub>s\<^sub>t (Insert t s#A) I D = dbupd\<^sub>s\<^sub>s\<^sub>t A I (insert ((t,s) \<cdot>\<^sub>p I) D)"
| "dbupd\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) I D = dbupd\<^sub>s\<^sub>s\<^sub>t A I (D - {((t,s) \<cdot>\<^sub>p I)})"
| "dbupd\<^sub>s\<^sub>s\<^sub>t (_#A) I D = dbupd\<^sub>s\<^sub>s\<^sub>t A I D"

fun db'\<^sub>s\<^sub>s\<^sub>t::"('f,'v) stateful_strand \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) dbstatelist \<Rightarrow> ('f,'v) dbstatelist"
where
  "db'\<^sub>s\<^sub>s\<^sub>t [] I D = D"
| "db'\<^sub>s\<^sub>s\<^sub>t (Insert t s#A) I D = db'\<^sub>s\<^sub>s\<^sub>t A I (List.insert ((t,s) \<cdot>\<^sub>p I) D)"
| "db'\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) I D = db'\<^sub>s\<^sub>s\<^sub>t A I (List.removeAll ((t,s) \<cdot>\<^sub>p I) D)"
| "db'\<^sub>s\<^sub>s\<^sub>t (_#A) I D = db'\<^sub>s\<^sub>s\<^sub>t A I D"

definition db\<^sub>s\<^sub>s\<^sub>t where
  "db\<^sub>s\<^sub>s\<^sub>t S I \<equiv> db'\<^sub>s\<^sub>s\<^sub>t S I []"

fun setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert t s) = {(t,s)}"
| "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete t s) = {(t,s)}"
| "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ t s) = {(t,s)}"
| "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks _ _ F') = set F'"
| "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p _ = {}"

text \<open>The set-operations of a stateful strand\<close>
definition setops\<^sub>s\<^sub>s\<^sub>t where
  "setops\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p ` set S)"

fun setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Insert t s) = [(t,s)]"
| "setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Delete t s) = [(t,s)]"
| "setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (InSet _ t s) = [(t,s)]"
| "setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks _ _ F') = F'"
| "setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p _ = []"

text \<open>The set-operations of a stateful strand (list variant)\<close>
definition setops_list\<^sub>s\<^sub>s\<^sub>t where
  "setops_list\<^sub>s\<^sub>s\<^sub>t S \<equiv> remdups (concat (map setops_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p S))"


subsection \<open>Small Lemmata\<close>
lemma is_Check_or_Assignment_iff[simp]:
  "is_Check x \<or> is_Assignment x \<longleftrightarrow> is_Check_or_Assignment x"
by (cases x) (blast intro: poscheckvariant.exhaust)+

lemma subst_apply_stateful_strand_step_Inequality[simp]:
  "\<langle>t != s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<langle>t \<cdot> \<theta> != s \<cdot> \<theta>\<rangle>"
  "\<forall>x\<langle>t != s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x\<langle>t \<cdot> rm_vars {x} \<theta> != s \<cdot> rm_vars {x} \<theta>\<rangle>"
  "\<forall>x,y\<langle>t != s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x,y\<langle>t \<cdot> rm_vars {x,y} \<theta> != s \<cdot> rm_vars {x,y} \<theta>\<rangle>"
  "\<forall>x,y,z\<langle>t != s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x,y,z\<langle>t \<cdot> rm_vars {x,y,z} \<theta> != s \<cdot> rm_vars {x,y,z} \<theta>\<rangle>"
by simp_all

lemma subst_apply_stateful_strand_step_NotInSet[simp]:
  "\<langle>t not in s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<langle>t \<cdot> \<theta> not in s \<cdot> \<theta>\<rangle>"
  "\<forall>x\<langle>t not in s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x\<langle>t \<cdot> rm_vars {x} \<theta> not in s \<cdot> rm_vars {x} \<theta>\<rangle>"
  "\<forall>x,y\<langle>t not in s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x,y\<langle>t \<cdot> rm_vars {x,y} \<theta> not in s \<cdot> rm_vars {x,y} \<theta>\<rangle>"
  "\<forall>x,y,z\<langle>t not in s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>x,y,z\<langle>t \<cdot> rm_vars {x,y,z} \<theta> not in s \<cdot> rm_vars {x,y,z} \<theta>\<rangle>"
by simp_all

lemma trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t: "trms\<^sub>s\<^sub>s\<^sub>t S = set (trms_list\<^sub>s\<^sub>s\<^sub>t S)"
unfolding trms\<^sub>s\<^sub>t_def trms_list\<^sub>s\<^sub>s\<^sub>t_def
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma setops_list\<^sub>s\<^sub>s\<^sub>t_is_setops\<^sub>s\<^sub>s\<^sub>t: "setops\<^sub>s\<^sub>s\<^sub>t S = set (setops_list\<^sub>s\<^sub>s\<^sub>t S)"
unfolding setops\<^sub>s\<^sub>s\<^sub>t_def setops_list\<^sub>s\<^sub>s\<^sub>t_def
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p: "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = set (fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)"
proof (cases a)
  case (NegChecks X F G) thus ?thesis
    using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_append[of F G] fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_append[of F G]
          fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of "F@G"]
    by auto
qed (simp_all add: fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s fv_list_is_fv)

lemma fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t: "fv\<^sub>s\<^sub>s\<^sub>t S = set (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
unfolding fv\<^sub>s\<^sub>s\<^sub>t_def fv_list\<^sub>s\<^sub>s\<^sub>t_def by (induct S) (simp_all add: fv_list\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p)

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite[simp]: "finite (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) auto

lemma trms\<^sub>s\<^sub>s\<^sub>t_finite[simp]: "finite (trms\<^sub>s\<^sub>s\<^sub>t S)"
using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by (induct S) auto

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite[simp]: "finite (vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) auto

lemma vars\<^sub>s\<^sub>s\<^sub>t_finite[simp]: "finite (vars\<^sub>s\<^sub>s\<^sub>t S)"
using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite unfolding vars\<^sub>s\<^sub>s\<^sub>t_def by (induct S) auto

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite[simp]: "finite (fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) auto

lemma fv\<^sub>s\<^sub>s\<^sub>t_finite[simp]: "finite (fv\<^sub>s\<^sub>s\<^sub>t S)"
using fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite unfolding fv\<^sub>s\<^sub>s\<^sub>t_def by (induct S) auto

lemma bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite[simp]: "finite (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x))"
by (rule finite_set)

lemma bvars\<^sub>s\<^sub>s\<^sub>t_finite[simp]: "finite (bvars\<^sub>s\<^sub>s\<^sub>t S)"
using bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_finite unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def by (induct S) auto

lemma subst_sst_nil[simp]: "[] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> = []"
by (simp add: subst_apply_stateful_strand_def)

lemma db\<^sub>s\<^sub>s\<^sub>t_nil[simp]: "db\<^sub>s\<^sub>s\<^sub>t [] \<I> = []"
by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def)

lemma ik\<^sub>s\<^sub>s\<^sub>t_nil[simp]: "ik\<^sub>s\<^sub>s\<^sub>t [] = {}"
by (simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

lemma in_ik\<^sub>s\<^sub>s\<^sub>t_iff: "t \<in> ik\<^sub>s\<^sub>s\<^sub>t A \<longleftrightarrow> (\<exists>ts. receive\<langle>ts\<rangle> \<in> set A \<and> t \<in> set ts)"
unfolding ik\<^sub>s\<^sub>s\<^sub>t_def by blast

lemma ik\<^sub>s\<^sub>s\<^sub>t_append[simp]: "ik\<^sub>s\<^sub>s\<^sub>t (A@B) = ik\<^sub>s\<^sub>s\<^sub>t A \<union> ik\<^sub>s\<^sub>s\<^sub>t B"
by (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

lemma ik\<^sub>s\<^sub>s\<^sub>t_concat: "ik\<^sub>s\<^sub>s\<^sub>t (concat xs) = \<Union>(ik\<^sub>s\<^sub>s\<^sub>t ` set xs)"
by (induct xs) auto

lemma ik\<^sub>s\<^sub>s\<^sub>t_subst: "ik\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) = ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
proof (induction A)
  case (Cons a A)
  have "ik\<^sub>s\<^sub>s\<^sub>t ([a] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) = ik\<^sub>s\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
  proof (cases a)
    case (Receive ts) thus ?thesis
      using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "[a]"] in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "[a] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>"]
      unfolding subst_apply_stateful_strand_def by auto
  qed (simp_all add: ik\<^sub>s\<^sub>s\<^sub>t_def subst_apply_stateful_strand_def)
  thus ?case
    using Cons.IH ik\<^sub>s\<^sub>s\<^sub>t_append
    by (metis append_Cons append_Nil image_Un map_append subst_apply_stateful_strand_def) 
qed simp

lemma ik\<^sub>s\<^sub>s\<^sub>t_set_subset:
  "set A \<subseteq> set B \<Longrightarrow> ik\<^sub>s\<^sub>s\<^sub>t A \<subseteq> ik\<^sub>s\<^sub>s\<^sub>t B"
unfolding ik\<^sub>s\<^sub>s\<^sub>t_def by blast

lemma ik\<^sub>s\<^sub>s\<^sub>t_prefix_subset:
  "prefix A B \<Longrightarrow> ik\<^sub>s\<^sub>s\<^sub>t A \<subseteq> ik\<^sub>s\<^sub>s\<^sub>t B" (is "?P A B \<Longrightarrow> ?P' A B")
  "prefix A (C@D) \<Longrightarrow> \<not>prefix A C \<Longrightarrow> ik\<^sub>s\<^sub>s\<^sub>t C \<subseteq> ik\<^sub>s\<^sub>s\<^sub>t A" (is "?Q \<Longrightarrow> ?Q' \<Longrightarrow> ?Q''")
proof -
  show "?P A B \<Longrightarrow> ?P' A B" for A B by (metis set_mono_prefix ik\<^sub>s\<^sub>s\<^sub>t_set_subset)
  thus "?Q \<Longrightarrow> ?Q' \<Longrightarrow> ?Q''" by (metis prefixI prefix_same_cases)
qed

lemma ik\<^sub>s\<^sub>s\<^sub>t_snoc_no_receive_empty:
  assumes "\<forall>a \<in> set A. \<not>is_Receive a"
  shows "ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I = {}"
using assms in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ A] by fastforce

lemma ik\<^sub>s\<^sub>s\<^sub>t_snoc_no_receive_eq:
  assumes "\<nexists>s. a = receive\<langle>s\<rangle>"
  shows "ik\<^sub>s\<^sub>s\<^sub>t (A@[a]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
using assms ik\<^sub>s\<^sub>s\<^sub>t_snoc_no_receive_empty[of "[a]" \<I>] ik\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]"]
unfolding is_Receive_def by auto

lemma db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t: "set (db'\<^sub>s\<^sub>s\<^sub>t A I D) = dbupd\<^sub>s\<^sub>s\<^sub>t A I (set D)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix t s show "(t,s) \<in> ?A \<Longrightarrow> (t,s) \<in> ?B" by (induct rule: db'\<^sub>s\<^sub>s\<^sub>t.induct) auto
  qed

  show "?B \<subseteq> ?A"
  proof
    fix t s show "(t,s) \<in> ?B \<Longrightarrow> (t,s) \<in> ?A" by (induct arbitrary: D rule: dbupd\<^sub>s\<^sub>s\<^sub>t.induct) auto
  qed
qed

lemma db\<^sub>s\<^sub>s\<^sub>t_no_upd:
  assumes "\<forall>a \<in> set A. \<not>is_Insert a \<and> \<not>is_Delete a"
  shows "db'\<^sub>s\<^sub>s\<^sub>t A I D = D"
using assms
proof (induction A)
  case (Cons a A) thus ?case by (cases a) auto
qed simp

lemma db\<^sub>s\<^sub>s\<^sub>t_no_upd_append:
  assumes "\<forall>b \<in> set B. \<not>is_Insert b \<and> \<not>is_Delete b"
  shows "db'\<^sub>s\<^sub>s\<^sub>t A = db'\<^sub>s\<^sub>s\<^sub>t (A@B)"
  using assms
proof (induction A)
  case Nil thus ?case by (simp add: db\<^sub>s\<^sub>s\<^sub>t_no_upd)
next
  case (Cons a A) thus ?case by (cases a) simp_all
qed

lemma db\<^sub>s\<^sub>s\<^sub>t_append:
  "db'\<^sub>s\<^sub>s\<^sub>t (A@B) I D = db'\<^sub>s\<^sub>s\<^sub>t B I (db'\<^sub>s\<^sub>s\<^sub>t A I D)"
proof (induction A arbitrary: D)
  case (Cons a A) thus ?case by (cases a) auto
qed simp

lemma db\<^sub>s\<^sub>s\<^sub>t_in_cases:
  assumes "(t,s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t A I D)"
  shows "(t,s) \<in> set D \<or> (\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set A \<and> t = t' \<cdot> I \<and> s = s' \<cdot> I)"
  using assms
proof (induction A arbitrary: D)
  case (Cons a A) thus ?case by (cases a) fastforce+
qed simp

lemma db\<^sub>s\<^sub>s\<^sub>t_in_cases':
  assumes "(t,s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t A I D)"
    and "(t,s) \<notin> set D"
  shows "\<exists>B C t' s'. A = B@insert\<langle>t',s'\<rangle>#C \<and> t = t' \<cdot> I \<and> s = s' \<cdot> I \<and>
                     (\<forall>t'' s''. delete\<langle>t'',s''\<rangle> \<in> set C \<longrightarrow> t \<noteq> t'' \<cdot> I \<or> s \<noteq> s'' \<cdot> I)"
  using assms(1)
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  note * = snoc db\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]" I D]
  thus ?case
  proof (cases a)
    case (Insert t' s')
    thus ?thesis using * by (cases "(t,s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t A I D)") force+
  next
    case (Delete t' s')
    hence **: "t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I" using * by simp

    have "(t,s) \<in> set (db'\<^sub>s\<^sub>s\<^sub>t A I D)" using * Delete by force
    then obtain B C u v where B:
        "A = B@insert\<langle>u,v\<rangle>#C" "t = u \<cdot> I" "s = v \<cdot> I"
        "\<forall>t' s'. delete\<langle>t',s'\<rangle> \<in> set C \<longrightarrow> t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I"
      using snoc.IH by moura

    have "A@[a] = B@insert\<langle>u,v\<rangle>#(C@[a])"
         "\<forall>t' s'. delete\<langle>t',s'\<rangle> \<in> set (C@[a]) \<longrightarrow> t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I"
      using B(1,4) Delete ** by auto
    thus ?thesis using B(2,3) by blast
  qed force+
qed (simp add: assms(2))

lemma db\<^sub>s\<^sub>s\<^sub>t_filter:
  "db'\<^sub>s\<^sub>s\<^sub>t A I D = db'\<^sub>s\<^sub>s\<^sub>t (filter is_Update A) I D"
by (induct A I D rule: db'\<^sub>s\<^sub>s\<^sub>t.induct) simp_all

lemma db\<^sub>s\<^sub>s\<^sub>t_subst_swap:
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>s\<^sub>t A. I x = J x"
  shows "db'\<^sub>s\<^sub>s\<^sub>t A I D = db'\<^sub>s\<^sub>s\<^sub>t A J D"
using assms
proof (induction A arbitrary: D)
  case (Cons a A)
  hence "\<forall>x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. I x = J x" "\<And>D. db'\<^sub>s\<^sub>s\<^sub>t A I D = db'\<^sub>s\<^sub>s\<^sub>t A J D" by auto
  thus ?case by (cases a) (simp_all add: term_subst_eq[of _ I J])
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd:
  assumes "\<forall>a \<in> set A. \<not>is_Insert a \<and> \<not>is_Delete a"
  shows "dbupd\<^sub>s\<^sub>s\<^sub>t A I D = D"
using assms
proof (induction A)
  case (Cons a A) thus ?case by (cases a) auto
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_no_deletes:
  assumes "list_all (\<lambda>a. \<not>is_Delete a) A"
  shows "dbupd\<^sub>s\<^sub>s\<^sub>t A I D = D \<union> {(t \<cdot> I, s \<cdot> I) | t s. insert\<langle>t,s\<rangle> \<in> set A}" (is "?Q A D")
using assms
proof (induction A arbitrary: D)
  case (Cons a A)
  hence IH: "?Q A D" for D by auto
  have "\<not>is_Delete a" using Cons.prems by simp
  thus ?case using IH by (cases a) auto
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_append:
  "dbupd\<^sub>s\<^sub>s\<^sub>t (A@B) I D = dbupd\<^sub>s\<^sub>s\<^sub>t B I (dbupd\<^sub>s\<^sub>s\<^sub>t A I D)"
proof (induction A arbitrary: D)
  case (Cons a A) thus ?case by (cases a) auto
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_filter:
  "dbupd\<^sub>s\<^sub>s\<^sub>t A I D = dbupd\<^sub>s\<^sub>s\<^sub>t (filter is_Update A) I D"
by (induct A I D rule: dbupd\<^sub>s\<^sub>s\<^sub>t.induct) simp_all

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_in_cases:
  assumes "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D"
  shows "(t,s) \<in> D \<or> (\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set A \<and> t = t' \<cdot> I \<and> s = s' \<cdot> I)" (is ?P)
    and "\<forall>u v B. suffix (delete\<langle>u,v\<rangle>#B) A \<and> (t,s) = (u,v) \<cdot>\<^sub>p I \<longrightarrow>
                  (\<exists>u' v'. (t,s) = (u',v') \<cdot>\<^sub>p I \<and> insert\<langle>u',v'\<rangle> \<in> set B)" (is ?Q)
proof -
  show ?P using assms
  proof (induction A arbitrary: D)
    case (Cons a A) thus ?case by (cases a) fastforce+
  qed simp

  show ?Q using assms
  proof (induction A arbitrary: D rule: List.rev_induct)
    case (snoc a A)
    note 0 = snoc.IH snoc.prems
    note 1 = suffix_snoc[of _ A a]

    have 2: "dbupd\<^sub>s\<^sub>s\<^sub>t (A@[a]) I D = dbupd\<^sub>s\<^sub>s\<^sub>t A I D" when "\<not>is_Update a"
      using that dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]" I D] by (cases a) auto

    have 3: "suffix (delete\<langle>u,v\<rangle>#B) A \<Longrightarrow> suffix (delete\<langle>u,v\<rangle>#B@[a]) (A@[a])"
      when "\<not>is_Update a" for u v B
      using that by simp

    have 4: "\<exists>C. B = C@[a] \<and> suffix (delete\<langle>u,v\<rangle>#C) A"
      when a: "\<not>is_Delete a" "suffix (delete\<langle>u,v\<rangle>#B) (A@[a])" for u v B
    proof -
      have a': "a \<noteq> delete\<langle>u,v\<rangle>" using a(1) by force
      obtain C where C: "delete\<langle>u,v\<rangle>#B = C@[a]" "suffix C A" using 1 a(2) by blast
      show ?thesis using a' C by (cases C) auto
    qed

    note 5 = dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]" I]

    show ?case
    proof (cases "is_Update a")
      case True
      then obtain u v where "a = insert\<langle>u,v\<rangle> \<or> a = delete\<langle>u,v\<rangle>" by (cases a) auto
      thus ?thesis
      proof
        assume a: "a = insert\<langle>u,v\<rangle>"
        hence a': "\<not>is_Delete a" by simp

        have 6: "insert\<langle>u,v\<rangle> \<in> set B"
          when B: "suffix (delete\<langle>u',v'\<rangle>#B) (A@[a])" for u' v' B
          using 4[OF a' B] unfolding a by fastforce

        have 7: "(t,s) = (u,v) \<cdot>\<^sub>p I \<or> (t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" using snoc.prems 5 a by auto
        show ?thesis
        proof (cases "(t,s) = (u,v) \<cdot>\<^sub>p I")
          case True
          have "insert\<langle>u,v\<rangle> \<in> set B"
            when B: "suffix (delete\<langle>u',v'\<rangle>#B) (A@[a])" for u' v' B
            using 4[OF a' B] unfolding a by fastforce
          thus ?thesis using True by blast
        next
          case False
          hence 8: "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" using 7 by blast
          have "\<exists>u'' v''. (t,s) = (u'',v'') \<cdot>\<^sub>p I \<and> insert\<langle>u'',v''\<rangle> \<in> set B"
            when B: "suffix (delete\<langle>u',v'\<rangle>#B) (A @ [a])" "(t,s) = (u',v') \<cdot>\<^sub>p I" for u' v' B
          proof -
            obtain C where C: "B = C@[a]" "suffix (delete\<langle>u',v'\<rangle>#C) A" using 4[OF a' B(1)] by blast
            thus ?thesis using snoc.IH[OF 8] B(2) unfolding a by fastforce
          qed
          thus ?thesis by blast
        qed
      next
        assume a: "a = delete\<langle>u,v\<rangle>"
        hence "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D - {((u,v) \<cdot>\<^sub>p I)}" using snoc.prems 5 by auto
        hence 6: "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" "(t,s) \<noteq> (u,v) \<cdot>\<^sub>p I" by (blast,blast)
        
        have "(\<exists>C. B = C@[a] \<and> suffix (delete\<langle>u',v'\<rangle>#C) A) \<or> (B = [] \<and> u' = u \<and> v' = v)"
          when B: "suffix (delete\<langle>u',v'\<rangle>#B) (A@[a])" for B u' v'
        proof -
          obtain C where C: "delete\<langle>u',v'\<rangle>#B = C@[a]" "suffix C A" using B 1 by blast
          show ?thesis
          proof (cases "B = []")
            case True thus ?thesis using C unfolding a by simp
          next
            case False
            then obtain b B' where B': "B = B'@[b]" by (meson rev_exhaust)
            show ?thesis using C unfolding a B' by auto
          qed 
        qed
        hence "\<exists>C. B = C@[a] \<and> suffix (delete\<langle>u',v'\<rangle>#C) A"
          when "suffix (delete\<langle>u',v'\<rangle>#B) (A@[a])" "(t,s) = (u',v') \<cdot>\<^sub>p I" for B u' v'
          using that 6 by blast
        thus ?thesis using snoc.IH[OF 6(1)] unfolding a by fastforce
      qed
    next
      case False
      have "\<exists>u' v'. (t,s) = (u',v') \<cdot>\<^sub>p I \<and> insert\<langle>u',v'\<rangle> \<in> set B"
        when B: "suffix (delete\<langle>u,v\<rangle>#B) (A@[a])" "(t,s) = (u,v) \<cdot>\<^sub>p I" for u v B
      proof -
        obtain C where C: "B = C@[a]" "suffix (delete\<langle>u,v\<rangle>#C) A" using 4[OF _ B(1)] False by blast
        show ?thesis using B(2) snoc.IH[OF snoc.prems[unfolded 2[OF False]]] C by fastforce
      qed
      thus ?thesis by blast
    qed
  qed simp
qed

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_in_iff:
  "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D \<longleftrightarrow>
   ((\<forall>u v B. suffix (delete\<langle>u,v\<rangle>#B) A \<and> (t,s) = (u,v) \<cdot>\<^sub>p I \<longrightarrow>
              (\<exists>u' v'. (t,s) = (u',v') \<cdot>\<^sub>p I \<and> insert\<langle>u',v'\<rangle> \<in> set B)) \<and>
    ((t,s) \<in> D \<or> (\<exists>u v. (t,s) = (u,v) \<cdot>\<^sub>p I \<and> insert\<langle>u,v\<rangle> \<in> set A)))"
  (is "?P A D \<longleftrightarrow> ?Q1 A \<and> ?Q2 A D")
proof
  show "?P A D \<Longrightarrow> ?Q1 A \<and> ?Q2 A D" using dbupd\<^sub>s\<^sub>s\<^sub>t_in_cases by fast

  show "?Q1 A \<and> ?Q2 A D \<Longrightarrow> ?P A D"
  proof (induction A arbitrary: D)
    case (Cons a A)
    have Q1: "?Q1 A" using Cons.prems suffix_Cons[of _ a A] by blast

    show ?case
    proof (cases "is_Update a")
      case False thus ?thesis using Q1 Cons.IH Cons.prems by (cases a) auto
    next
      case True
      then obtain t' s' where "a = insert\<langle>t',s'\<rangle> \<or> a = delete\<langle>t',s'\<rangle>" by (cases a) auto
      thus ?thesis
      proof
        assume a: "a = insert\<langle>t',s'\<rangle>"
        hence "?Q2 A (insert ((t',s') \<cdot>\<^sub>p I) D)" using Cons.prems by auto
        thus ?thesis using Q1 Cons.IH unfolding a by auto
      next
        assume a: "a = delete\<langle>t',s'\<rangle>"
        hence "?Q2 A (D - {(t',s') \<cdot>\<^sub>p I})" using Cons.prems by auto
        thus ?thesis using Q1 Cons.IH unfolding a by auto
      qed
    qed
  qed simp
qed

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_in_cases':
  fixes A::"('a,'b) stateful_strand"
  assumes "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D"
    and "(t,s) \<notin> D"
  shows "\<exists>B C t' s'. A = B@insert\<langle>t',s'\<rangle>#C \<and> t = t' \<cdot> I \<and> s = s' \<cdot> I \<and>
                     (\<forall>t'' s''. delete\<langle>t'',s''\<rangle> \<in> set C \<longrightarrow> t \<noteq> t'' \<cdot> I \<or> s \<noteq> s'' \<cdot> I)"
using assms(1)
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  note 0 = dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]" I D]
  have 1: "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" when "\<not>is_Update a" using that snoc.prems 0 by (cases a) auto
  show ?case
  proof (cases "is_Update a")
    case False
    obtain B C t' s' where B:
        "A = B@insert\<langle>t',s'\<rangle>#C" "t = t' \<cdot> I" "s = s' \<cdot> I"
        "\<forall>t'' s''. delete\<langle>t'',s''\<rangle> \<in> set C \<longrightarrow> t \<noteq> t'' \<cdot> I \<or> s \<noteq> s'' \<cdot> I"
      using snoc.IH[OF 1[OF False]] by blast

    have "A@[a] = B@insert\<langle>t',s'\<rangle>#(C@[a])"
         "\<forall>t'' s''. delete\<langle>t'',s''\<rangle> \<in> set (C@[a]) \<longrightarrow> t \<noteq> t'' \<cdot> I \<or> s \<noteq> s'' \<cdot> I"
      using False B(1,4) by auto
    thus ?thesis using B(2,3) by blast
  next
    case True
    then obtain t' s' where "a = insert\<langle>t',s'\<rangle> \<or> a = delete\<langle>t',s'\<rangle>" by (cases a) auto
    thus ?thesis
    proof
      assume a: "a = insert\<langle>t',s'\<rangle>"
      hence "dbupd\<^sub>s\<^sub>s\<^sub>t (A@[a]) I D = insert ((t',s') \<cdot>\<^sub>p I) (dbupd\<^sub>s\<^sub>s\<^sub>t A I D)" using 0 by simp
      hence "(t,s) = (t',s') \<cdot>\<^sub>p I \<or> (t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" using snoc.prems by blast
      thus ?thesis
      proof
        assume 2: "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" show ?thesis using snoc.IH[OF 2] unfolding a by force
      qed (force simp add: a)
    next
      assume a: "a = delete\<langle>t',s'\<rangle>"
      hence 2: "t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I" using 0 snoc.prems by simp
  
      have "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D" using 0 snoc.prems a by force
      then obtain B C u v where B:
          "A = B@insert\<langle>u,v\<rangle>#C" "t = u \<cdot> I" "s = v \<cdot> I"
          "\<forall>t' s'. delete\<langle>t',s'\<rangle> \<in> set C \<longrightarrow> t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I"
        using snoc.IH by moura
  
      have "A@[a] = B@insert\<langle>u,v\<rangle>#(C@[a])"
           "\<forall>t' s'. delete\<langle>t',s'\<rangle> \<in> set (C@[a]) \<longrightarrow> t \<noteq> t' \<cdot> I \<or> s \<noteq> s' \<cdot> I"
        using B(1,4) a 2 by auto
      thus ?thesis using B(2,3) by blast
    qed
  qed
qed (simp add: assms(2))

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_mono:
  assumes "D \<subseteq> E"
  shows "dbupd\<^sub>s\<^sub>s\<^sub>t A I D \<subseteq> dbupd\<^sub>s\<^sub>s\<^sub>t A I E"
using assms
proof (induction A arbitrary: D E)
  case (Cons a A) thus ?case
  proof (cases a)
    case (Insert t s)
    have "insert ((t,s) \<cdot>\<^sub>p I) D \<subseteq> insert ((t,s) \<cdot>\<^sub>p I) E" using Cons.prems by fast
    thus ?thesis using Cons.IH unfolding Insert by simp
  next
    case (Delete t s)
    have "D - {(t,s) \<cdot>\<^sub>p I} \<subseteq> E - {(t,s) \<cdot>\<^sub>p I}" using Cons.prems by fast
    thus ?thesis using Cons.IH unfolding Delete by simp
  qed auto
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_db_narrow:
  assumes "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I (D \<union> E)"
    and "(t,s) \<notin> D"
  shows "(t,s) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I E"
using assms
proof (induction A arbitrary: D E)
  case (Cons a A) thus ?case
  proof (cases a)
    case (Delete t' s') thus ?thesis
      using Cons.prems Cons.IH[of "D - {(t',s') \<cdot>\<^sub>p I}" "E - {(t',s') \<cdot>\<^sub>p I}"] by (simp add: Un_Diff)
  qed auto
qed simp

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_set_term_neq_in_iff:
  assumes f: "f \<noteq> k"
    and A: "\<forall>t s. insert\<langle>t,s\<rangle> \<in> set A \<longrightarrow> (\<exists>g ts. s = Fun g ts)"
  shows "(t,Fun f ts) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A I D \<longleftrightarrow>
         (t,Fun f ts) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t (filter (\<lambda>a. \<nexists>s ss. a = insert\<langle>s,Fun k ss\<rangle>) A) I D"
    (is "?P A D \<longleftrightarrow> ?P (?f A) D")
proof
  show "?P A D \<Longrightarrow> ?P (?f A) D" using A
  proof (induction A arbitrary: D)
    case (Cons a A)
    have IH: "?P A D \<Longrightarrow> ?P (?f A) D" for D
      using Cons.prems(2) Cons.IH by simp

    show ?case
    proof (cases "is_Update a")
      case True
      then obtain u s where "a = insert\<langle>u,s\<rangle> \<or> a = delete\<langle>u,s\<rangle>" by (cases a) auto
      thus ?thesis
      proof
        assume a: "a = insert\<langle>u,s\<rangle>"
        obtain g ss where s: "s = Fun g ss" using a Cons.prems(2) by fastforce

        have 0: "?P A (insert ((u, s) \<cdot>\<^sub>p I) D)" using a Cons.prems(1) by fastforce
        show ?thesis
        proof (cases "g = k")
          case g: True
          have "?f (a#A) = ?f A" unfolding a s g by force
          moreover have "(t,Fun f ts) \<noteq> (u, Fun g ss) \<cdot>\<^sub>p I" using f unfolding g by auto
          ultimately show ?thesis
            using IH[OF 0] dbupd\<^sub>s\<^sub>s\<^sub>t_db_narrow[of t "Fun f ts" "?f A" I "{(u, s) \<cdot>\<^sub>p I}" D]
            unfolding a s g by force
        next
          case g: False
          have "?f (a#A) = a#?f A" using g unfolding a s by force
          thus ?thesis using Cons.prems Cons.IH g unfolding a s by force
        qed
      next
        assume a: "a = delete\<langle>u,s\<rangle>"
        hence "?f (a#A) = a#?f A" by auto
        thus ?thesis using Cons.prems Cons.IH unfolding a by fastforce
      qed
    next
      case a: False
      hence "?P A D" using Cons.prems(1) by (cases a) auto
      hence "?P (?f A) D" using Cons.IH Cons.prems(2) a by fastforce
      thus ?thesis using a by (cases a) auto
    qed
  qed simp

  have "dbupd\<^sub>s\<^sub>s\<^sub>t (?f A) I D \<subseteq> dbupd\<^sub>s\<^sub>s\<^sub>t A I D"
  proof (induction A arbitrary: D)
    case (Cons a A) show ?case
    proof (cases a)
      case (Insert t s)
      have "?f (a#A) = a#?f A \<or> ?f (a#A) = ?f A" unfolding Insert by force
      hence "dbupd\<^sub>s\<^sub>s\<^sub>t (?f (a#A)) I D \<subseteq> dbupd\<^sub>s\<^sub>s\<^sub>t (?f A) I (insert ((t,s) \<cdot>\<^sub>p I) D)"
        using dbupd\<^sub>s\<^sub>s\<^sub>t_mono[of D "insert ((t, s) \<cdot>\<^sub>p I) D"] unfolding Insert by auto
      thus ?thesis using Cons.IH unfolding Insert by fastforce
    qed (use Cons.prems Cons.IH in auto)
  qed simp
  thus "?P (?f A) D \<Longrightarrow> ?P A D" by blast
qed

lemma dbupd\<^sub>s\<^sub>s\<^sub>t_subst_const_swap:
  fixes t s
  defines "fvs \<equiv> \<lambda>A D. fv\<^sub>s\<^sub>s\<^sub>t A \<union> fv t \<union> fv s \<union> \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r ` D)"
  assumes "(t \<cdot> \<delta>, s \<cdot> \<delta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)" (is "?in \<delta> A D")
    and "\<forall>x \<in> fvs A D.
          \<delta> x = \<theta> x \<or>
          (\<not>(\<delta> x \<sqsubseteq> t) \<and> \<not>(\<delta> x \<sqsubseteq> s) \<and> \<not>(\<theta> x \<sqsubseteq> t) \<and> \<not>(\<theta> x \<sqsubseteq> s) \<and>
           (\<forall>(u,v) \<in> D. \<not>(\<delta> x \<sqsubseteq> u) \<and> \<not>(\<delta> x \<sqsubseteq> v) \<and> \<not>(\<theta> x \<sqsubseteq> u) \<and> \<not>(\<theta> x \<sqsubseteq> v)) \<and>
           (\<forall>u v. insert\<langle>u,v\<rangle> \<in> set A \<or> delete\<langle>u,v\<rangle> \<in> set A \<longrightarrow>
                    \<not>(\<delta> x \<sqsubseteq> u) \<and> \<not>(\<delta> x \<sqsubseteq> v) \<and> \<not>(\<theta> x \<sqsubseteq> u) \<and> \<not>(\<theta> x \<sqsubseteq> v)))"
      (is "?A \<delta> \<theta> D")
    and "\<forall>x \<in> fvs A D. \<exists>c. \<delta> x = Fun c []" (is "?B \<delta>")
    and "\<forall>x \<in> fvs A D. \<exists>c. \<theta> x = Fun c []" (is "?B \<theta>")
    and "\<forall>x \<in> fvs A D. \<forall>y \<in> fvs A D. \<delta> x = \<delta> y \<longleftrightarrow> \<theta> x = \<theta> y" (is "?C \<delta> \<theta> A D")
  shows "(t \<cdot> \<theta>, s \<cdot> \<theta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)" (is "?in \<theta> A D")
using assms(2-)
proof (induction A arbitrary: D rule: List.rev_induct)
  case Nil
  then obtain u v where u: "(u,v) \<in> D" "t \<cdot> \<delta> = u \<cdot> \<delta>" "s \<cdot> \<delta> = v \<cdot> \<delta>" by auto

  let ?X = "fv t \<union> fv u"
  let ?Y = "fv s \<union> fv v"

  have 0: "fv u \<subseteq> fvs [] D" "fv v \<subseteq> fvs [] D" "fv t \<subseteq> fvs [] D" "fv s \<subseteq> fvs [] D"
    using u(1) unfolding fvs_def by (blast, blast, blast, blast)

  have 1: "\<forall>x \<in> ?X. \<delta> x = \<theta> x \<or> (\<not>(\<delta> x \<sqsubseteq> t) \<and> \<not>(\<delta> x \<sqsubseteq> u))"
          "\<forall>x \<in> ?Y. \<delta> x = \<theta> x \<or> (\<not>(\<delta> x \<sqsubseteq> s) \<and> \<not>(\<delta> x \<sqsubseteq> v))"
    using Nil.prems(2) u(1) unfolding fvs_def by (blast,blast)

  have 2: "\<forall>x \<in> ?X. \<exists>c. \<delta> x = Fun c []" "\<forall>x \<in> ?X. \<exists>c. \<theta> x = Fun c []"
          "\<forall>x \<in> ?Y. \<exists>c. \<delta> x = Fun c []" "\<forall>x \<in> ?Y. \<exists>c. \<theta> x = Fun c []"
    using Nil.prems(3,4) 0 by (blast,blast,blast,blast)

  have 3: "\<forall>x \<in> ?X. \<forall>y \<in> ?X. \<delta> x = \<delta> y \<longleftrightarrow> \<theta> x = \<theta> y"
          "\<forall>x \<in> ?Y. \<forall>y \<in> ?Y. \<delta> x = \<delta> y \<longleftrightarrow> \<theta> x = \<theta> y"
    using Nil.prems(5) 0 by (blast,blast)

  have "t \<cdot> \<theta> = u \<cdot> \<theta>" "s \<cdot> \<theta> = v \<cdot> \<theta>"
    using subst_const_swap_eq'[OF u(2) 1(1) 2(1,2) 3(1)]
          subst_const_swap_eq'[OF u(3) 1(2) 2(3,4) 3(2)]
    by argo+
  thus ?case using u(1) by force
next
  case (snoc a A)
  have 0: "fvs A D \<subseteq> fvs (A@[a]) D" "set A \<subseteq> set (A@[a])" unfolding fvs_def by auto

  note 1 = dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]"]

  have IH: "(t \<cdot> \<delta>, s \<cdot> \<delta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>) \<Longrightarrow> (t \<cdot> \<theta>, s \<cdot> \<theta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    using snoc.IH[of D] snoc.prems(2-) 0 by blast

  let ?q0 = "\<lambda>t s \<delta> \<theta>. \<forall>x \<in> fv t \<union> fv s. \<delta> x = \<theta> x \<or> (\<not>(\<delta> x \<sqsubseteq> t) \<and> \<not>(\<delta> x \<sqsubseteq> s))"
  let ?q1 = "\<lambda>t s \<delta>.   \<forall>x \<in> fv t \<union> fv s. \<exists>c. \<delta> x = Fun c []"
  let ?q2 = "\<lambda>t s \<delta> \<theta>. \<forall>x \<in> fv t \<union> fv s. \<forall>y \<in> fv t \<union> fv s. \<delta> x = \<delta> y \<longleftrightarrow> \<theta> x = \<theta> y"

  show ?case
  proof (cases "is_Update a")
    case False
    hence "dbupd\<^sub>s\<^sub>s\<^sub>t (A@[a]) \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>) = dbupd\<^sub>s\<^sub>s\<^sub>t A \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
          "dbupd\<^sub>s\<^sub>s\<^sub>t (A@[a]) \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>) = dbupd\<^sub>s\<^sub>s\<^sub>t A \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)"
      using 1 by (cases a; auto)+
    thus ?thesis using IH snoc.prems(1) by blast
  next
    case True
    then obtain u v where u: "a = insert\<langle>u,v\<rangle> \<or> a = delete\<langle>u,v\<rangle>" by (cases a) auto

    have uv_in: "insert\<langle>u,v\<rangle> \<in> set (A@[a]) \<or> delete\<langle>u,v\<rangle> \<in> set (A@[a])" using u by force
    hence fv_uv: "fv u \<subseteq> fvs (A@[a]) D" "fv v \<subseteq> fvs (A@[a]) D" unfolding fvs_def by (force,force)

    have fv_ts: "fv t \<subseteq> fvs (A@[a]) D" "fv s \<subseteq> fvs (A@[a]) D" unfolding fvs_def by (blast,blast)

    have q0: "?q0 t u \<delta> \<theta>" "?q0 s v \<delta> \<theta>"
             "?q0 t u \<theta> \<delta>" "?q0 s v \<theta> \<delta>"
    proof -
      show "?q0 t u \<delta> \<theta>" "?q0 s v \<delta> \<theta>"
        using snoc.prems(2) 0 fv_ts fv_uv uv_in by (blast,blast)

      show "?q0 t u \<theta> \<delta>"
      proof
        fix x assume "x \<in> fv t \<union> fv u"
        hence "x \<in> fvs (A@[a]) D" using fv_ts(1) fv_uv(1) by blast
        thus "\<theta> x = \<delta> x \<or> (\<not>(\<theta> x \<sqsubseteq> t) \<and> \<not>(\<theta> x \<sqsubseteq> u))" 
          using snoc.prems(2) uv_in by auto
      qed

      show "?q0 s v \<theta> \<delta>"
      proof
        fix x assume "x \<in> fv s \<union> fv v"
        hence "x \<in> fvs (A@[a]) D" using fv_ts(2) fv_uv(2) by blast
        thus "\<theta> x = \<delta> x \<or> (\<not>(\<theta> x \<sqsubseteq> s) \<and> \<not>(\<theta> x \<sqsubseteq> v))" 
          using snoc.prems(2) uv_in by auto
      qed
    qed

    have q1: "?q1 t u \<delta>" "?q1 t u \<theta>"
             "?q1 s v \<delta>" "?q1 s v \<theta>"
      using snoc.prems(3,4) 0 fv_ts fv_uv by (blast,blast,blast,blast)

    have q2: "?q2 t u \<delta> \<theta>" "?q2 s v \<delta> \<theta>"
             "?q2 t u \<theta> \<delta>" "?q2 s v \<theta> \<delta>"
      using snoc.prems(5) 0 fv_ts fv_uv by (blast,blast,blast,blast)

    from u show ?thesis
    proof
      assume a: "a = insert\<langle>u,v\<rangle>"
      show ?thesis
      proof (cases "(t \<cdot> \<delta>, s \<cdot> \<delta>) = (u,v) \<cdot>\<^sub>p \<delta>")
        case True
        hence "(t \<cdot> \<theta>, s \<cdot> \<theta>) = (u,v) \<cdot>\<^sub>p \<theta>"
          using subst_const_swap_eq'[OF _ q0(1) q1(1,2) q2(1)]
                subst_const_swap_eq'[OF _ q0(2) q1(3,4) q2(2)]
          by fast
        thus ?thesis using 1 unfolding a by simp
      next
        case False
        hence "(t \<cdot> \<delta>, s \<cdot> \<delta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
          using snoc.prems(1) 1 unfolding a by force
        hence "(t \<cdot> \<theta>, s \<cdot> \<theta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)"
          using IH by blast
        thus ?thesis using 1 unfolding a by simp
      qed
    next
      assume a: "a = delete\<langle>u,v\<rangle>"
      have "(t \<cdot> \<delta>, s \<cdot> \<delta>) \<noteq> (u,v) \<cdot>\<^sub>p \<delta>"
        using snoc.prems(1) dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]"] unfolding a by fastforce
      hence 2: "(t \<cdot> \<theta>, s \<cdot> \<theta>) \<noteq> (u,v) \<cdot>\<^sub>p \<theta>"
        using subst_const_swap_eq'[OF _ q0(3) q1(2,1) q2(3)]
              subst_const_swap_eq'[OF _ q0(4) q1(4,3) q2(4)]
        by fast

      have "(t \<cdot> \<delta>, s \<cdot> \<delta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<delta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
        using snoc.prems(1) 1 unfolding a by fastforce
      hence 3: "(t \<cdot> \<theta>, s \<cdot> \<theta>) \<in> dbupd\<^sub>s\<^sub>s\<^sub>t A \<theta> (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)"
        using IH by blast

      show ?thesis using 2 3 dbupd\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]"] unfolding a by auto
    qed
  qed
qed

lemma subst_sst_cons: "a#A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> = (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)#(A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (simp add: subst_apply_stateful_strand_def)

lemma subst_sst_snoc: "A@[a] \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> = (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)@[a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>]"
by (simp add: subst_apply_stateful_strand_def)

lemma subst_sst_append[simp]: "A@B \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> = (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)@(B \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (simp add: subst_apply_stateful_strand_def)

lemma subst_sst_list_all:
  "list_all is_Send S \<longleftrightarrow> list_all is_Send (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Receive S \<longleftrightarrow> list_all is_Receive (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Equality S \<longleftrightarrow> list_all is_Equality (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Insert S \<longleftrightarrow> list_all is_Insert (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Delete S \<longleftrightarrow> list_all is_Delete (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_InSet S \<longleftrightarrow> list_all is_InSet (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_NegChecks S \<longleftrightarrow> list_all is_NegChecks (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Assignment S \<longleftrightarrow> list_all is_Assignment (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Check S \<longleftrightarrow> list_all is_Check (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Update S \<longleftrightarrow> list_all is_Update (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  "list_all is_Check_or_Assignment S \<longleftrightarrow> list_all is_Check_or_Assignment (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
proof (induction S)
  case (Cons x S)
  note * = list_all_def subst_apply_stateful_strand_def
  { case 1 thus ?case using Cons.IH(1) unfolding * by (cases x) auto }
  { case 2 thus ?case using Cons.IH(2) unfolding * by (cases x) auto }
  { case 3 thus ?case using Cons.IH(3) unfolding * by (cases x) auto }
  { case 4 thus ?case using Cons.IH(4) unfolding * by (cases x) auto }
  { case 5 thus ?case using Cons.IH(5) unfolding * by (cases x) auto }
  { case 6 thus ?case using Cons.IH(6) unfolding * by (cases x) auto }
  { case 7 thus ?case using Cons.IH(7) unfolding * by (cases x) auto }
  { case 8 thus ?case using Cons.IH(8) unfolding * by (cases x) fastforce+ }
  { case 9 thus ?case using Cons.IH(9) unfolding * by (cases x) auto }
  { case 10 thus ?case using Cons.IH(10) unfolding * by (cases x) auto }
  { case 11 thus ?case using Cons.IH(11) unfolding * by (cases x) auto }
qed simp_all

lemma subst_sstp_id_subst: "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p Var = a"
by (cases a) auto

lemma subst_sst_id_subst: "A \<cdot>\<^sub>s\<^sub>s\<^sub>t Var = A"
by (induct A) (simp, metis subst_sstp_id_subst subst_sst_cons)

lemma sst_vars_append_subset:
  "fv\<^sub>s\<^sub>s\<^sub>t A \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (A@B)" "bvars\<^sub>s\<^sub>s\<^sub>t A \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (A@B)"
  "fv\<^sub>s\<^sub>s\<^sub>t B \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (A@B)" "bvars\<^sub>s\<^sub>s\<^sub>t B \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (A@B)"
by auto

lemma sst_vars_disj_cons[simp]: "fv\<^sub>s\<^sub>s\<^sub>t (a#A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (a#A) = {} \<Longrightarrow> fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma fv\<^sub>s\<^sub>s\<^sub>t_cons_subset[simp]: "fv\<^sub>s\<^sub>s\<^sub>t A \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (a#A)"
by auto

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases[simp]:
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<doteq> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<in> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) =
    fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) - set X"
by simp_all

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_cases[simp]:
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<doteq> s\<rangle>) = fv t \<union> fv s"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle>) = fv t \<union> fv s"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle>) = fv t \<union> fv s"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<in> s\<rangle>) = fv t \<union> fv s"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<union> set X" (is ?A)
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: [(t,s)] \<or>\<notin>: []\<rangle>) = fv t \<union> fv s \<union> set X" (is ?B)
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: [] \<or>\<notin>: [(t,s)]\<rangle>) = fv t \<union> fv s \<union> set X" (is ?C)
proof
  show ?A ?B ?C by auto
qed simp_all

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases[simp]:
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<doteq> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<in> s\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (s \<cdot> \<theta>)"
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) =
    fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> set X" (is ?A)
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: [(t,s)] \<or>\<notin>: []\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) =
    fv (t \<cdot> rm_vars (set X) \<theta>) \<union> fv (s \<cdot> rm_vars (set X) \<theta>) \<union> set X" (is ?B)
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: [] \<or>\<notin>: [(t,s)]\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) =
    fv (t \<cdot> rm_vars (set X) \<theta>) \<union> fv (s \<cdot> rm_vars (set X) \<theta>) \<union> set X" (is ?C)
proof
  show ?A ?B ?C by auto
qed simp_all

lemma bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset: "bvars\<^sub>s\<^sub>s\<^sub>t A \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (a#A)"
by auto

lemma bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst: "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
by (cases a) auto

lemma bvars\<^sub>s\<^sub>s\<^sub>t_subst: "bvars\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>s\<^sub>t A"
using bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[of _ \<delta>]
by (induct A) (simp_all add: subst_apply_stateful_strand_def)

lemma bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_set_cases[simp]:
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<doteq> s\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>c: t \<in> s\<rangle>)) = {}"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)) = set X"
by simp_all

lemma bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegChecks: "\<not>is_NegChecks a \<Longrightarrow> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = []"
by (cases a) simp_all

lemma bvars\<^sub>s\<^sub>s\<^sub>t_NegChecks: "bvars\<^sub>s\<^sub>s\<^sub>t A = bvars\<^sub>s\<^sub>s\<^sub>t (filter is_NegChecks A)" 
proof (induction A)
  case (Cons a A) thus ?case by (cases a) fastforce+
qed simp

lemma vars\<^sub>s\<^sub>s\<^sub>t_append[simp]: "vars\<^sub>s\<^sub>s\<^sub>t (A@B) = vars\<^sub>s\<^sub>s\<^sub>t A \<union> vars\<^sub>s\<^sub>s\<^sub>t B"
by (simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)

lemma vars\<^sub>s\<^sub>s\<^sub>t_Nil[simp]: "vars\<^sub>s\<^sub>s\<^sub>t [] = {}"
by (simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)

lemma vars\<^sub>s\<^sub>s\<^sub>t_Cons: "vars\<^sub>s\<^sub>s\<^sub>t (a#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
by (simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)

lemma fv\<^sub>s\<^sub>s\<^sub>t_Cons: "fv\<^sub>s\<^sub>s\<^sub>t (a#A) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<union> fv\<^sub>s\<^sub>s\<^sub>t A"
unfolding fv\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma bvars\<^sub>s\<^sub>s\<^sub>t_Cons: "bvars\<^sub>s\<^sub>s\<^sub>t (a#A) = set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<union> bvars\<^sub>s\<^sub>s\<^sub>t A"
unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma vars\<^sub>s\<^sub>s\<^sub>t_Cons'[simp]:
  "vars\<^sub>s\<^sub>s\<^sub>t (send\<langle>ts\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (send\<langle>ts\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (receive\<langle>ts\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (receive\<langle>ts\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (\<langle>a: t \<doteq> s\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>a: t \<doteq> s\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (insert\<langle>t,s\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,s\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (delete\<langle>t,s\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (delete\<langle>t,s\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (\<langle>a: t \<in> s\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>a: t \<in> s\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
  "vars\<^sub>s\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<union> vars\<^sub>s\<^sub>s\<^sub>t A"
by (simp_all add: vars\<^sub>s\<^sub>s\<^sub>t_def)

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_if_no_bvars:
  assumes a: "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = []"
  shows "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)"
proof (cases a)
  case (NegChecks X F G)
  hence "set X = {}" using a by fastforce
  thus ?thesis using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of _ \<theta>] unfolding NegChecks by simp
qed (auto simp add: subst_list_set_fv subst_apply_fv_unfold)

lemma fv\<^sub>s\<^sub>s\<^sub>t_subst_if_no_bvars:
  assumes A: "bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  shows "fv\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv\<^sub>s\<^sub>s\<^sub>t A)"
using assms
proof (induction A)
  case (Cons a A) thus ?case
    using fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_if_no_bvars[of a \<theta>] fv\<^sub>s\<^sub>s\<^sub>t_Cons[of a A] bvars\<^sub>s\<^sub>s\<^sub>t_Cons[of a A]
          subst_sst_cons[of a A \<theta>]
    by simp
qed simp

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  fixes x::"('a,'b) stateful_strand_step"
  shows "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<union> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x)"
proof (cases x)
  case (NegChecks X F G) thus ?thesis by (induct F) force+
qed simp_all

lemma vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t:
  fixes S::"('a,'b) stateful_strand"
  shows "vars\<^sub>s\<^sub>s\<^sub>t S = fv\<^sub>s\<^sub>s\<^sub>t S \<union> bvars\<^sub>s\<^sub>s\<^sub>t S"
proof (induction S)
  case (Cons x S) thus ?case
    using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p[of x]
    by (auto simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)
qed simp

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[simp]:
  "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) = set X \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
by (simp_all add: sup_commute sup_left_commute vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p)

lemma bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[simp]:
  "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) = X"
  "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>[]\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)) = {}"
by simp_all

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[simp]:
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G - set X"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<forall>[]\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>t != s\<rangle>) = fv t \<union> fv s"
  "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>t not in s\<rangle>) = fv t \<union> fv s"
by simp_all

lemma fv\<^sub>s\<^sub>s\<^sub>t_append[simp]: "fv\<^sub>s\<^sub>s\<^sub>t (A@B) = fv\<^sub>s\<^sub>s\<^sub>t A \<union> fv\<^sub>s\<^sub>s\<^sub>t B"
by simp

lemma bvars\<^sub>s\<^sub>s\<^sub>t_append[simp]: "bvars\<^sub>s\<^sub>s\<^sub>t (A@B) = bvars\<^sub>s\<^sub>s\<^sub>t A \<union> bvars\<^sub>s\<^sub>s\<^sub>t B"
by auto

lemma fv\<^sub>s\<^sub>s\<^sub>t_mono: "set A \<subseteq> set B \<Longrightarrow> fv\<^sub>s\<^sub>s\<^sub>t A \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t B"
by auto

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  assumes "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
  shows "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)"
using assms var_is_subterm
proof (cases a)
  case (NegChecks X F F')
  hence "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' - set X" using assms by simp
  thus ?thesis using NegChecks var_is_subterm by fastforce
qed force+

lemma fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t A \<Longrightarrow> Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t A)"
proof (induction A)
  case (Cons a A) thus ?case using fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p by (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t A") auto
qed simp

lemma var_subterm_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  assumes "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)"
  shows "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
using assms vars_iff_subtermeq
proof (cases a)
  case (NegChecks X F F')
  hence "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F')" using assms by simp
  thus ?thesis using NegChecks vars_iff_subtermeq by force
qed force+

lemma var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  show ?case
  proof (cases "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t A)")
    case True thus ?thesis using Cons.IH by (simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)
  next
    case False thus ?thesis
      using Cons.prems var_subterm_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p
      by (fastforce simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)
  qed
qed simp

lemma var_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t: "Var x \<in> trms\<^sub>s\<^sub>s\<^sub>t A \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>s\<^sub>t A"
by (meson var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t UN_I term.order_refl)

lemma ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset: "ik\<^sub>s\<^sub>s\<^sub>t A \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A"
by (force simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

lemma var_subterm_ik\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>s\<^sub>t A"
using var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset by fast

lemma var_subterm_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t:
  assumes "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t A)"
  shows "x \<in> fv\<^sub>s\<^sub>s\<^sub>t A"
proof -
  obtain ts where ts: "Receive ts \<in> set A" "Var x \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts"
    using assms unfolding ik\<^sub>s\<^sub>s\<^sub>t_def by moura
  hence "fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t A" unfolding fv\<^sub>s\<^sub>s\<^sub>t_def by force
  thus ?thesis using ts(2) subterm_is_var by fastforce
qed

lemma fv_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t:
  assumes "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t A)"
  shows "x \<in> fv\<^sub>s\<^sub>s\<^sub>t A"
using var_subterm_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t assms var_is_subterm by fastforce

lemma fv_trms\<^sub>s\<^sub>s\<^sub>t_subset:
  "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t S"
  "fv\<^sub>s\<^sub>s\<^sub>t S \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
proof (induction S)
  case (Cons x S)
  have *: "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t (x#S)) = fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x) \<union> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
          "fv\<^sub>s\<^sub>s\<^sub>t (x#S) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<union> fv\<^sub>s\<^sub>s\<^sub>t S" "vars\<^sub>s\<^sub>s\<^sub>t (x#S) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<union> vars\<^sub>s\<^sub>s\<^sub>t S"
    unfolding trms\<^sub>s\<^sub>s\<^sub>t_def fv\<^sub>s\<^sub>s\<^sub>t_def vars\<^sub>s\<^sub>s\<^sub>t_def
    by auto

  { case 1
    show ?case using Cons.IH(1)
    proof (cases x)
      case (NegChecks X F G)
      hence "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
            "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<union> set X"
        by (simp, meson vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_cases(7))
      hence "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x"
        using fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of F] fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of G]
        by auto
      thus ?thesis
        using Cons.IH(1) *(1,3)
        by blast
    qed auto
  }

  { case 2
    show ?case using Cons.IH(2)
    proof (cases x)
      case (NegChecks X F G)
      hence "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
            "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G) - set X"
        by auto
      hence "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p x)"
        using fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of F] fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of G]
        by auto
      thus ?thesis
        using Cons.IH(2) *(1,2)
        by blast
    qed auto
  }
qed simp_all

lemma fv_ik_subset_fv_sst'[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t S) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
unfolding ik\<^sub>s\<^sub>s\<^sub>t_def by (induct S) auto

lemma fv_ik_subset_vars_sst'[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t S) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t S"
using fv_ik_subset_fv_sst' fv_trms\<^sub>s\<^sub>s\<^sub>t_subset by fast

lemma ik\<^sub>s\<^sub>s\<^sub>t_var_is_fv: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> x \<in> fv\<^sub>s\<^sub>s\<^sub>t A"
by (meson fv_ik_subset_fv_sst'[of A] fv_subset_subterms subsetCE term.set_intros(3))

lemma vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases':
  assumes x: "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  shows "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s \<or> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)"
using x vars_term_subst[of _ \<theta>] vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_cases(1,2,3,4,5,6) vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(1,2)[of _ \<theta>]
      vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(3,6)[of _ _ _ \<theta>] vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(4,5)[of _ _ \<theta>]
proof (cases s)
  case (NegChecks X F G)
  let ?\<theta>' = "rm_vars (set X) \<theta>"
  have "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>') \<or> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>') \<or> x \<in> set X"
    using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(7)[of X F G \<theta>] x NegChecks by simp
  hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (?\<theta>' ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<or> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (?\<theta>' ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G) \<or> x \<in> set X"
    using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of _ ?\<theta>'] by blast
  hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<or> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G) \<or> x \<in> set X"
    using rm_vars_fv\<^sub>s\<^sub>e\<^sub>t_subst by fast
  thus ?thesis
    using NegChecks vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_cases(7)[of X F G]
    by auto
qed simp_all

lemma vars\<^sub>s\<^sub>s\<^sub>t_subst_cases:
  assumes "x \<in> vars\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  shows "x \<in> vars\<^sub>s\<^sub>s\<^sub>t S \<or> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` vars\<^sub>s\<^sub>s\<^sub>t S)"
  using assms
proof (induction S)
  case (Cons s S) thus ?case
  proof (cases "x \<in> vars\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)")
    case False
    note * = subst_sst_cons[of s S \<theta>] vars\<^sub>s\<^sub>s\<^sub>t_Cons[of "s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>" "S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>"] vars\<^sub>s\<^sub>s\<^sub>t_Cons[of s S]
    have **: "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)" using Cons.prems False * by simp
    show ?thesis using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases'[OF **] * by auto
  qed (auto simp add: vars\<^sub>s\<^sub>s\<^sub>t_def)
qed simp

lemma subset_subst_pairs_diff_exists:
  fixes \<I>::"('a,'b) subst" and D D'::"('a,'b) dbstate"
  shows "\<exists>Di. Di \<subseteq> D \<and> Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> = (D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - D'"
by (metis (no_types, lifting) Diff_subset subset_image_iff)

lemma subset_subst_pairs_diff_exists':
  fixes \<I>::"('a,'b) subst" and D::"('a,'b) dbstate"
  assumes "finite D"
  shows "\<exists>Di. Di \<subseteq> D \<and> Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {d \<cdot>\<^sub>p \<I>} \<and> d \<cdot>\<^sub>p \<I> \<notin> (D - Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
using assms
proof (induction D rule: finite_induct)
  case (insert d' D)
  then obtain Di where IH: "Di \<subseteq> D" "Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {d \<cdot>\<^sub>p \<I>}" "d \<cdot>\<^sub>p \<I> \<notin> (D - Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" by moura
  show ?case
  proof (cases "d' \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>")
    case True
    hence "insert d' Di \<subseteq> insert d' D" "insert d' Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {d \<cdot>\<^sub>p \<I>}"
          "d \<cdot>\<^sub>p \<I> \<notin> (insert d' D - insert d' Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" 
      using IH by auto
    thus ?thesis by metis
  next
    case False
    hence "Di \<subseteq> insert d' D" "Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {d \<cdot>\<^sub>p \<I>}"
          "d \<cdot>\<^sub>p \<I> \<notin> (insert d' D - Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" 
      using IH by auto
    thus ?thesis by metis
  qed
qed simp

lemma stateful_strand_step_subst_inI[intro]:
  "send\<langle>ts\<rangle> \<in> set A \<Longrightarrow> send\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "receive\<langle>ts\<rangle> \<in> set A \<Longrightarrow> receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "\<langle>c: t \<doteq> s\<rangle> \<in> set A \<Longrightarrow> \<langle>c: (t \<cdot> \<theta>) \<doteq> (s \<cdot> \<theta>)\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "insert\<langle>t, s\<rangle> \<in> set A \<Longrightarrow> insert\<langle>t \<cdot> \<theta>, s \<cdot> \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "delete\<langle>t, s\<rangle> \<in> set A \<Longrightarrow> delete\<langle>t \<cdot> \<theta>, s \<cdot> \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "\<langle>c: t \<in> s\<rangle> \<in> set A \<Longrightarrow> \<langle>c: (t \<cdot> \<theta>) \<in> (s \<cdot> \<theta>)\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set A 
    \<Longrightarrow> \<forall>X\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<or>\<notin>: (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "\<langle>t != s\<rangle> \<in> set A \<Longrightarrow> \<langle>t \<cdot> \<theta> != s \<cdot> \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "\<langle>t not in s\<rangle> \<in> set A \<Longrightarrow> \<langle>t \<cdot> \<theta> not in s \<cdot> \<theta>\<rangle> \<in> set (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
proof (induction A)
  case (Cons a A)
  note * = subst_sst_cons[of a A \<theta>]
  { case 1 thus ?case using Cons.IH(1) * by (cases a) auto }
  { case 2 thus ?case using Cons.IH(2) * by (cases a) auto }
  { case 3 thus ?case using Cons.IH(3) * by (cases a) auto }
  { case 4 thus ?case using Cons.IH(4) * by (cases a) auto }
  { case 5 thus ?case using Cons.IH(5) * by (cases a) auto }
  { case 6 thus ?case using Cons.IH(6) * by (cases a) auto }
  { case 7 thus ?case using Cons.IH(7) * by (cases a) auto }
  { case 8 thus ?case using Cons.IH(8) * by (cases a) auto }
  { case 9 thus ?case using Cons.IH(9) * by (cases a) auto }
qed simp_all

lemma stateful_strand_step_cases_subst:
  "is_Send a = is_Send (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Receive a = is_Receive (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Equality a = is_Equality (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Insert a = is_Insert (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Delete a = is_Delete (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_InSet a = is_InSet (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_NegChecks a = is_NegChecks (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Assignment a = is_Assignment (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Check a = is_Check (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Update a = is_Update (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
  "is_Check_or_Assignment a = is_Check_or_Assignment (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
by (cases a; simp_all)+

lemma stateful_strand_step_substD:
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = send\<langle>ts\<rangle> \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> a = send\<langle>ts'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = receive\<langle>ts\<rangle> \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> a = receive\<langle>ts'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = \<langle>c: t \<doteq> s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = \<langle>c: t' \<doteq> s'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = insert\<langle>t,s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = insert\<langle>t',s'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = delete\<langle>t,s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = delete\<langle>t',s'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = \<langle>c: t \<in> s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = \<langle>c: t' \<in> s'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<Longrightarrow>
    \<exists>F' G'. F = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and> G = G' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and>
            a = \<forall>X\<langle>\<or>\<noteq>: F' \<or>\<notin>: G'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = \<langle>t != s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = \<langle>t' != s'\<rangle>"
  "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = \<langle>t not in s\<rangle> \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = \<langle>t' not in s'\<rangle>"
by (cases a; auto simp add: subst_apply_pairs_def; fail)+

lemma stateful_strand_step_mem_substD:
  "send\<langle>ts\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> send\<langle>ts'\<rangle> \<in> set S"
  "receive\<langle>ts\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> receive\<langle>ts'\<rangle> \<in> set S"
  "\<langle>c: t \<doteq> s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> \<langle>c: t' \<doteq> s'\<rangle> \<in> set S"
  "insert\<langle>t,s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> insert\<langle>t',s'\<rangle> \<in> set S"
  "delete\<langle>t,s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> delete\<langle>t',s'\<rangle> \<in> set S"
  "\<langle>c: t \<in> s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> \<langle>c: t' \<in> s'\<rangle> \<in> set S"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>F' G'. F = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and> G = G' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and>
            \<forall>X\<langle>\<or>\<noteq>: F' \<or>\<notin>: G'\<rangle> \<in> set S"
  "\<langle>t != s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> \<langle>t' != s'\<rangle> \<in> set S"
  "\<langle>t not in s\<rangle> \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> \<langle>t' not in s'\<rangle> \<in> set S"
proof (induction S)
  case (Cons a S)
  have *: "x \<in> set (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>)"
    when "x \<in> set (a#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>)" "x \<noteq> a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>" for x
    using that by (simp add: subst_apply_stateful_strand_def)

  { case 1 thus ?case using Cons.IH(1)[OF *] by (cases a) auto }
  { case 2 thus ?case using Cons.IH(2)[OF *] by (cases a) auto }
  { case 3 thus ?case using Cons.IH(3)[OF *] by (cases a) auto }
  { case 4 thus ?case using Cons.IH(4)[OF *] by (cases a) auto }
  { case 5 thus ?case using Cons.IH(5)[OF *] by (cases a) auto }
  { case 6 thus ?case using Cons.IH(6)[OF *] by (cases a) auto }
  { case 7 thus ?case using Cons.IH(7)[OF *] by (cases a) auto }
  { case 8 show ?case
    proof (cases a)
      case (NegChecks Y F' G') thus ?thesis
      proof (cases "\<langle>t != s\<rangle> = a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>")
        case True thus ?thesis using NegChecks stateful_strand_step_substD(8)[of a \<sigma> t s] by force
      qed (use 8 Cons.IH(8)[OF *] in auto)
    qed (use 8 Cons.IH(8)[OF *] in simp_all)
  }
  { case 9 show ?case
    proof (cases a)
      case (NegChecks Y F' G') thus ?thesis
      proof (cases "\<langle>t not in s\<rangle> = a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>")
        case True thus ?thesis using NegChecks stateful_strand_step_substD(9)[of a \<sigma> t s] by force
      qed (use 9 Cons.IH(9)[OF *] in auto)
    qed (use 9 Cons.IH(9)[OF *] in simp_all)
  }
qed simp_all

lemma stateful_strand_step_fv_subset_cases:
  "send\<langle>ts\<rangle> \<in> set S \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "receive\<langle>ts\<rangle> \<in> set S \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>c: t \<doteq> s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "insert\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "delete\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>c: t \<in> s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set S \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G - set X \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>t != s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>t not in s\<rangle> \<in> set S \<Longrightarrow> fv t \<union> fv s \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t S"
proof (induction S)
  case (Cons a S)
  { case 1 thus ?case using Cons.IH(1) by auto }
  { case 2 thus ?case using Cons.IH(2) by auto }
  { case 3 thus ?case using Cons.IH(3) by auto }
  { case 4 thus ?case using Cons.IH(4) by auto }
  { case 5 thus ?case using Cons.IH(5) by auto }
  { case 6 thus ?case using Cons.IH(6) by auto }
  { case 7 thus ?case using Cons.IH(7) by fastforce }
  { case 8 thus ?case using Cons.IH(8) by fastforce }
  { case 9 thus ?case using Cons.IH(9) by fastforce }
qed simp_all

lemma trms\<^sub>s\<^sub>s\<^sub>t_nil[simp]:
  "trms\<^sub>s\<^sub>s\<^sub>t [] = {}"
unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_mono:
  "set M \<subseteq> set N \<Longrightarrow> trms\<^sub>s\<^sub>s\<^sub>t M \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t N"
by auto

lemma trms\<^sub>s\<^sub>s\<^sub>t_memI[intro?]:
  "send\<langle>ts\<rangle> \<in> set S \<Longrightarrow> t \<in> set ts \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "receive\<langle>ts\<rangle> \<in> set S \<Longrightarrow> t \<in> set ts \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>ac: t \<doteq> s\<rangle> \<in> set S \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "\<langle>ac: t \<doteq> s\<rangle> \<in> set S \<Longrightarrow> s \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "insert\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "insert\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> s \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "delete\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "delete\<langle>t,s\<rangle> \<in> set S \<Longrightarrow> s \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set S \<Longrightarrow> t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set S \<Longrightarrow> t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by fastforce+

lemma trms\<^sub>s\<^sub>s\<^sub>t_in:
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t S"
  shows "\<exists>a \<in> set S. t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
using assms unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_cons: "trms\<^sub>s\<^sub>s\<^sub>t (a#A) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<union> trms\<^sub>s\<^sub>s\<^sub>t A"
unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by force

lemma trms\<^sub>s\<^sub>s\<^sub>t_append[simp]: "trms\<^sub>s\<^sub>s\<^sub>t (A@B) = trms\<^sub>s\<^sub>s\<^sub>t A \<union> trms\<^sub>s\<^sub>s\<^sub>t B"
unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by force

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst:
  assumes "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<inter> subst_domain \<theta> = {}"
  shows "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
proof (cases a)
  case (NegChecks X F G)
  hence "rm_vars (set X) \<theta> = \<theta>" using assms rm_vars_apply'[of \<theta> "set X"] by auto
  hence "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
        "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    using NegChecks image_Un by simp_all
  thus ?thesis by (metis trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst)
qed simp_all

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst':
  assumes "\<not>is_NegChecks a"
  shows "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms by (cases a) simp_all

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst'':
  fixes t::"('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
  shows "\<exists>s \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. t = s \<cdot> rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta>"
proof (cases "is_NegChecks b")
  case True
  then obtain X F G where *: "b = NegChecks X F G" by (cases b) moura+
  thus ?thesis using assms trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of _ "rm_vars (set X) \<delta>"] by auto
next
  case False
  hence "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta>"
    using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst' bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegChecks
    by fastforce
  thus ?thesis using assms by fast
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst''':
  fixes t::"('a,'b) term" and \<delta> \<theta>::"('a,'b) subst"
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  shows "\<exists>s \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. t = s \<cdot> rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta> \<circ>\<^sub>s \<theta>"
proof -
  obtain s where s: "s \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)" "t = s \<cdot> \<theta>" using assms by moura
  show ?thesis using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst''[OF s(1)] s(2) by auto
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes "bvars\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}"
  shows "trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = trms\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms
proof (induction S)
  case (Cons a S)
  hence IH: "trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = trms\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" and *: "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<inter> subst_domain \<theta> = {}"
    by auto
  show ?case using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[OF *] IH by (auto simp add: subst_apply_stateful_strand_def)
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_subst_cons:
  "trms\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> trms\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
using subst_sst_cons[of a A \<delta>] trms\<^sub>s\<^sub>s\<^sub>t_cons[of a A] trms\<^sub>s\<^sub>s\<^sub>t_append by simp

lemma (in intruder_model) wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>))"
  using assms
proof (cases a)
  case (NegChecks X F G)
  hence *: "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) =
              (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)) \<union> (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>))"
    by simp

  have "trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> = (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<union> (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    using NegChecks image_Un by simp
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)" using * assms by auto
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<delta>)"
        "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<delta>)"
    using wf_trms_subst_rm_vars[of \<delta> "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" "set X"]
          wf_trms_subst_rm_vars[of \<delta> "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" "set X"]
    by fast+
  thus ?thesis
    using * trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of _ "rm_vars (set X) \<delta>"]
    by auto
qed auto

lemma trms\<^sub>s\<^sub>s\<^sub>t_fv_vars\<^sub>s\<^sub>s\<^sub>t_subset: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t A \<Longrightarrow> fv t \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t A" 
proof (induction A)
  case (Cons a A) thus ?case by (cases a) auto
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_fv_subst_subset:
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t S" "subst_domain \<theta> \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "fv (t \<cdot> \<theta>) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
using assms
proof (induction S)
  case (Cons s S) show ?case
  proof (cases "t \<in> trms\<^sub>s\<^sub>s\<^sub>t S")
    case True
    hence "fv (t \<cdot> \<theta>) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)" using Cons.IH Cons.prems by auto
    thus ?thesis using subst_sst_cons[of s S \<theta>] unfolding vars\<^sub>s\<^sub>s\<^sub>t_def by auto
  next
    case False
    hence *: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p s" "subst_domain \<theta> \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) = {}" using Cons.prems by auto
    hence "fv (t \<cdot> \<theta>) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
    proof (cases s)
      case (NegChecks X F G)
      hence **: "t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<or> t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" using *(1) by auto
      have ***: "rm_vars (set X) \<theta> = \<theta>" using *(2) NegChecks rm_vars_apply' by auto
      have "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"
        using ** *** trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fv_subst_subset[of t _ \<theta>] by auto
      thus ?thesis using *(2) using NegChecks vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(7)[of X F G \<theta>] by blast
    qed auto
    thus ?thesis using subst_sst_cons[of s S \<theta>] unfolding vars\<^sub>s\<^sub>s\<^sub>t_def by auto
  qed
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_fv_subst_subset':
  assumes "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)" "fv t \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}" "fv (t \<cdot> \<theta>) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
using assms
proof (induction S)
  case (Cons s S) show ?case
  proof (cases "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)")
    case True
    hence "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)" using Cons.IH Cons.prems by auto
    thus ?thesis using subst_sst_cons[of s S \<theta>] unfolding vars\<^sub>s\<^sub>s\<^sub>t_def by auto
  next
    case False
    hence 0: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)" "fv t \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) = {}"
             "fv (t \<cdot> \<theta>) \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) = {}"
      using Cons.prems by auto

    note 1 = UN_Un UN_insert fv\<^sub>s\<^sub>e\<^sub>t.simps subst_apply_fv_subset subst_apply_fv_unfold
             subst_apply_term_empty sup_bot.comm_neutral fv_subterms_set fv_subset[OF 0(1)]

    note 2 = subst_apply_fv_union

    have "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
    proof (cases s)
      case (Send ts)
      have "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set ts)" using fv_subset[OF 0(1)] unfolding Send fv_subterms_set by simp
      hence "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
        by (metis subst_apply_fv_subset subst_apply_fv_unfold_set)
      thus ?thesis using Send by simp
    next
      case (Receive ts)
      have "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set ts)" using fv_subset[OF 0(1)] unfolding Receive fv_subterms_set by simp
      hence "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
        by (metis subst_apply_fv_subset subst_apply_fv_unfold_set)
      thus ?thesis using Receive by simp
    next
      case (NegChecks X F G)
      hence 3: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<or> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G)" using 0(1) by auto
      have "t \<cdot> rm_vars (set X) \<theta> = t \<cdot> \<theta>" using 0(2) NegChecks rm_vars_ident[of t] by auto
      hence "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"
        using 3 trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fv_subst_subset'[of t _ "rm_vars (set X) \<theta>"] by fastforce
      thus ?thesis using 0(2,3) NegChecks fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(7)[of X F G \<theta>] by auto
    qed (metis (no_types, lifting) 1 2 trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(3) fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(3),
         metis (no_types, lifting) 1 2 trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(4) fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(4),
         metis (no_types, lifting) 1 2 trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(5) fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(5),
         metis (no_types, lifting) 1 2 trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(6) fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(6))
    thus ?thesis using subst_sst_cons[of s S \<theta>] unfolding fv\<^sub>s\<^sub>s\<^sub>t_def by auto
  qed
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_funs_term_cases:
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)" "f \<in> funs_term t"
  shows "(\<exists>u \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p s. f \<in> funs_term u) \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p s. f \<in> funs_term (\<theta> x))"
  using assms
proof (cases s)
  case (NegChecks X F G)
  hence "t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<or> t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"
    using assms(1) by auto
  hence "(\<exists>u\<in>trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. f \<in> funs_term u) \<or> (\<exists>x\<in>fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. f \<in> funs_term (rm_vars (set X) \<theta> x)) \<or>
         (\<exists>u\<in>trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G. f \<in> funs_term u) \<or> (\<exists>x\<in>fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G. f \<in> funs_term (rm_vars (set X) \<theta> x))"
    using trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_funs_term_cases[OF _ assms(2), of _ "rm_vars (set X) \<theta>"] by meson
  hence "(\<exists>u \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G. f \<in> funs_term u) \<or>
         (\<exists>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G. f \<in> funs_term (rm_vars (set X) \<theta> x))"
    by blast
  thus ?thesis
  proof
    assume "\<exists>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G. f \<in> funs_term (rm_vars (set X) \<theta> x)"
    then obtain x where x: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" "f \<in> funs_term (rm_vars (set X) \<theta> x)"
      by auto
    hence "x \<notin> set X" "rm_vars (set X) \<theta> x = \<theta> x" by auto
    thus ?thesis using x by (auto simp add: assms NegChecks)
  qed (auto simp add: assms NegChecks)
qed (use assms funs_term_subst[of _ \<theta>] in auto)

lemma trms\<^sub>s\<^sub>s\<^sub>t_funs_term_cases:
  assumes "t \<in> trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)" "f \<in> funs_term t"
  shows "(\<exists>u \<in> trms\<^sub>s\<^sub>s\<^sub>t S. f \<in> funs_term u) \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>s\<^sub>t S. f \<in> funs_term (\<theta> x))"
using assms(1)
proof (induction S)
  case (Cons s S) thus ?case
  proof (cases "t \<in> trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)")
    case False
    hence "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)" using Cons.prems(1) subst_sst_cons[of s S \<theta>] trms\<^sub>s\<^sub>s\<^sub>t_cons by auto
    thus ?thesis using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_funs_term_cases[OF _ assms(2)] by fastforce
  qed auto
qed simp

lemma fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes "x \<in> fv\<^sub>s\<^sub>s\<^sub>t T"
    and "bvars\<^sub>s\<^sub>s\<^sub>t T \<inter> subst_domain \<theta> = {}"
  shows "\<theta> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>))"
using trms\<^sub>s\<^sub>s\<^sub>t_subst[OF assms(2)] subterms_subst_subset'[of \<theta> "trms\<^sub>s\<^sub>s\<^sub>t T"]
      fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t[OF assms(1)]
by (metis (no_types, lifting) image_iff subset_iff eval_term.simps(1))

lemma fv\<^sub>s\<^sub>s\<^sub>t_subst_fv_subset:
  assumes "x \<in> fv\<^sub>s\<^sub>s\<^sub>t S" "x \<notin> bvars\<^sub>s\<^sub>s\<^sub>t S" "fv (\<theta> x) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
using assms
proof (induction S)
  case (Cons a S)
  note 1 = fv_subst_subset[of _ _ \<theta>]
  note 2 = subst_apply_fv_union subst_apply_fv_unfold[of _ \<theta>] fv_subset image_eqI
  note 3 = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases
  note 4 = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps
  from Cons show ?case
  proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t S")
    case False
    hence 5: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" " fv (\<theta> x) \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) = {}" "x \<notin> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)"
      using Cons.prems by auto
    hence "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
    proof (cases a)
      case (Send ts) thus ?thesis using 1 5(1) 3(1) 4(1) by auto
    next
      case (Receive ts) thus ?thesis using 1 5(1) 3(2) 4(2) by auto
    next
      case (NegChecks X F G)
      let ?\<delta> = "rm_vars (set X) \<theta>"
      have *: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" using NegChecks 5(1) by auto
      have **: "fv (\<theta> x) \<inter> set X = {}" using NegChecks 5(2) by simp
      have ***: "\<theta> x = ?\<delta> x" using NegChecks 5(3) by auto
      have "fv (\<theta> x) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<delta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<delta>)"
        using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_fv_subset[of x _ ?\<delta>] * *** by auto
      thus ?thesis using NegChecks ** by auto
    qed (metis (full_types) 2 5(1) 3(3) 4(3), metis (full_types) 2 5(1) 3(4) 4(4),
         metis (full_types) 2 5(1) 3(5) 4(5), metis (full_types) 2 5(1) 3(6) 4(6))
    thus ?thesis by (auto simp add: subst_sst_cons[of a S \<theta>])
  qed (auto simp add: subst_sst_cons[of a S \<theta>])
qed simp

lemma (in intruder_model) wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_trms\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>))"
  using assms
proof (induction A)
  case (Cons a A)
  hence IH: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>))" and *: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)" by auto
  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>))" by (rule wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[OF *])
  thus ?case using IH trms\<^sub>s\<^sub>s\<^sub>t_subst_cons[of a A \<delta>] by blast
qed simp

lemma fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var:
  assumes "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  shows "\<exists>y \<in> fv\<^sub>s\<^sub>s\<^sub>t S. x \<in> fv (\<delta> y)"
  using assms
proof (induction S)
  case (Cons s S)
  hence "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) \<Longrightarrow> \<exists>y \<in> fv\<^sub>s\<^sub>s\<^sub>t S. x \<in> fv (\<delta> y)"
    using bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset[of S s]
    by blast
  thus ?case
  proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)")
    case False
    hence *: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
      using Cons.prems(1) subst_sst_cons[of s S \<delta>]
      by fastforce

    have "\<exists>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p s. x \<in> fv (\<delta> y)"
    proof (cases s)
      case (NegChecks X F G)
      hence "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>) \<or> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)"
          and **: "x \<notin> set X"
        using * by simp_all
      then obtain y where y: "y \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<or> y \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" "x \<in> fv ((rm_vars (set X) \<delta>) y)"
        using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var[of _ _ "rm_vars (set X) \<delta>"]
        by blast
      have "y \<notin> set X"
      proof
        assume y_in: "y \<in> set X"
        hence "(rm_vars (set X) \<delta>) y = Var y" by auto
        hence "x = y" using y(2) by simp
        thus False using ** y_in by metis
      qed
      thus ?thesis using NegChecks y by auto
    qed (use * fv_subst_obtain_var in force)+
    thus ?thesis by auto
  qed auto
qed simp

lemma fv\<^sub>s\<^sub>s\<^sub>t_subst_subset_range_vars_if_subset_domain:
  assumes "fv\<^sub>s\<^sub>s\<^sub>t S \<subseteq> subst_domain \<sigma>"
  shows "fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<subseteq> range_vars \<sigma>"
using assms fv\<^sub>s\<^sub>s\<^sub>t_subst_obtain_var[of _ S \<sigma>] subst_dom_vars_in_subst[of _ \<sigma>] subst_fv_imgI[of \<sigma>]
by (metis (no_types) in_mono subsetI)

lemma fv\<^sub>s\<^sub>s\<^sub>t_in_fv_trms\<^sub>s\<^sub>s\<^sub>t: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t S \<Longrightarrow> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
proof (induction S)
  case (Cons s S) thus ?case
  proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t S")
    case False
    hence *: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p s" using Cons.prems by simp
    hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)"
    proof (cases s)
      case (NegChecks X F G)
      hence "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<or> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" using * by simp_all
      thus ?thesis using * fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_in_fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of x] NegChecks by auto
    qed auto
    thus ?thesis by simp
  qed simp
qed simp

lemma fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_ground_subst_compose:
  assumes "subst_domain \<delta> = subst_domain \<sigma>"
    and "range_vars \<delta> = {}" "range_vars \<sigma> = {}"
  shows "fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta>) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> \<circ>\<^sub>s \<theta>)"
proof -
  note 0 = fv_ground_subst_compose

  have 1: "range_vars \<delta> \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) = {}" "range_vars \<sigma> \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) = {}"
    using assms(2,3) by (blast,blast)

  note 2 = 0[OF assms, of _ \<theta>]

  show ?thesis
  proof (cases a)
    case (NegChecks X F G)
    have 3: "range_vars \<delta> \<inter> set X = {}" "range_vars (rm_vars (set X) \<delta>) = {}"
            "range_vars \<sigma> \<inter> set X = {}" "range_vars (rm_vars (set X) \<sigma>) = {}"
      using assms(2,3) rm_vars_img_fv_subset[of "set X"] by auto

    have 4: "subst_domain (rm_vars (set X) \<delta>) = subst_domain (rm_vars (set X) \<sigma>)"
      using assms(1) rm_vars_dom[of "set X"] by blast

    have 5: "fv (t \<cdot> rm_vars (set X) (\<delta> \<circ>\<^sub>s \<theta>)) = fv (t \<cdot> rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<theta>))" for t
      using 2[of t] rm_vars_comp[OF 3(1), of t \<theta>] rm_vars_comp[OF 3(3), of t \<theta>]
            0[OF 4 3(2,4), of t "rm_vars (set X) \<theta>"]
      by argo

    have 6: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (H \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) (\<delta> \<circ>\<^sub>s \<theta>)) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (H \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<theta>))"
      for H
    proof -
      have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r (h \<cdot>\<^sub>p rm_vars (set X) (\<delta> \<circ>\<^sub>s \<theta>)) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r (h \<cdot>\<^sub>p rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<theta>))" for h
      proof -
        obtain s t where h: "h = (s,t)" by (metis surj_pair)
        show ?thesis using 5[of s] 5[of t] unfolding h by fast
      qed
      thus ?thesis unfolding subst_apply_pairs_def by auto
    qed

    show ?thesis using 5 6 unfolding NegChecks by simp
  qed (use 2 in auto)
qed

lemma fv\<^sub>s\<^sub>s\<^sub>t_ground_subst_compose:
  assumes "subst_domain \<delta> = subst_domain \<sigma>"
    and "range_vars \<delta> = {}" "range_vars \<sigma> = {}"
  shows "fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta>) = fv\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<theta>)"
by (induct S) (auto simp add: fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_ground_subst_compose[OF assms] fv\<^sub>s\<^sub>s\<^sub>t_Cons subst_sst_cons)

lemma stateful_strand_step_subst_comp:
  assumes "range_vars \<delta> \<inter> set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p x) = {}"
  shows "x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta> = (x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>"
proof (cases x)
  case (NegChecks X F G)
  hence *: "range_vars \<delta> \<inter> set X = {}" using assms by simp
  have "H \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) (\<delta> \<circ>\<^sub>s \<theta>) = (H \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>) \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>" for H
    using pairs_subst_comp rm_vars_comp[OF *] by (induct H) (auto simp add: subst_apply_pairs_def)
  thus ?thesis using NegChecks by simp
qed simp_all

lemma stateful_strand_subst_comp:
  assumes "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>"
using assms
proof (induction S)
  case (Cons s S)
  hence IH: "S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>" using Cons by auto

  have "s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta> = (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>"
    using Cons.prems stateful_strand_step_subst_comp[of \<delta> s \<theta>]
    unfolding range_vars_alt_def by auto
  thus ?case using IH by (simp add: subst_apply_stateful_strand_def)
qed simp

lemma subst_apply_bvars_disj_NegChecks:
  assumes "set X \<inter> subst_domain \<theta> = {}"
  shows "NegChecks X F G \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = NegChecks X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
proof -
  have "rm_vars (set X) \<theta> = \<theta>" using assms rm_vars_apply'[of \<theta> "set X"] by auto
  thus ?thesis by simp
qed

lemma subst_apply_NegChecks_no_bvars[simp]:
  "\<forall>[]\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>[]\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) \<or>\<notin>: (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)\<rangle>"
  "\<forall>[]\<langle>\<or>\<noteq>: [] \<or>\<notin>: F'\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>[]\<langle>\<or>\<noteq>: [] \<or>\<notin>: (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)\<rangle>"
  "\<forall>[]\<langle>\<or>\<noteq>: F \<or>\<notin>: []\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>[]\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) \<or>\<notin>: []\<rangle>"
  "\<forall>[]\<langle>\<or>\<noteq>: [] \<or>\<notin>: [(t,s)]\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>[]\<langle>\<or>\<noteq>: [] \<or>\<notin>: ([(t \<cdot> \<theta>,s \<cdot> \<theta>)])\<rangle>"
  "\<forall>[]\<langle>\<or>\<noteq>: [(t,s)] \<or>\<notin>: []\<rangle> \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta> = \<forall>[]\<langle>\<or>\<noteq>: ([(t \<cdot> \<theta>,s \<cdot> \<theta>)]) \<or>\<notin>: []\<rangle>"
by simp_all

lemma setops\<^sub>s\<^sub>s\<^sub>t_mono:
  "set M \<subseteq> set N \<Longrightarrow> setops\<^sub>s\<^sub>s\<^sub>t M \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t N"
by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_nil[simp]: "setops\<^sub>s\<^sub>s\<^sub>t [] = {}"
by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_cons[simp]: "setops\<^sub>s\<^sub>s\<^sub>t (a#A) = setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<union> setops\<^sub>s\<^sub>s\<^sub>t A"
by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_cons_subset[simp]: "setops\<^sub>s\<^sub>s\<^sub>t A \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (a#A)"
using setops\<^sub>s\<^sub>s\<^sub>t_cons[of a A] by blast

lemma setops\<^sub>s\<^sub>s\<^sub>t_append: "setops\<^sub>s\<^sub>s\<^sub>t (A@B) = setops\<^sub>s\<^sub>s\<^sub>t A \<union> setops\<^sub>s\<^sub>s\<^sub>t B"
proof (induction A)
  case (Cons a A) thus ?case by (cases a) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_member_iff:
  "(t,s) \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<longleftrightarrow>
    (x = Insert t s \<or> x = Delete t s \<or> (\<exists>ac. x = InSet ac t s) \<or>
     (\<exists>X F F'. x = NegChecks X F F' \<and> (t,s) \<in> set F'))"
by (cases x) auto

lemma setops\<^sub>s\<^sub>s\<^sub>t_member_iff:
  "(t,s) \<in> setops\<^sub>s\<^sub>s\<^sub>t A \<longleftrightarrow>
    (Insert t s \<in> set A \<or> Delete t s \<in> set A \<or> (\<exists>ac. InSet ac t s \<in> set A) \<or>
     (\<exists>X F F'. NegChecks X F F' \<in> set A \<and> (t,s) \<in> set F'))"
  (is "?P \<longleftrightarrow> ?Q")
proof (induction A)
  case (Cons a A) thus ?case
  proof (cases "(t, s) \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p a")
    case True thus ?thesis using setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_member_iff[of t s a] by auto
  qed auto
qed simp

lemma setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst:
  assumes "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<inter> subst_domain \<theta> = {}"
  shows "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
proof (cases a)
  case (NegChecks X F G)
  hence "rm_vars (set X) \<theta> = \<theta>" using assms rm_vars_apply'[of \<theta> "set X"] by auto
  hence "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = set (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
        "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta> = set G \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
    using NegChecks image_Un by simp_all
  thus ?thesis by (simp add: subst_apply_pairs_def) 
qed simp_all

lemma setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst':
  assumes "\<not>is_NegChecks a"
  shows "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms by (cases a) auto

lemma setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst'':
  fixes t::"('a,'b) term \<times> ('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes t: "t \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
  shows "\<exists>s \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. t = s \<cdot>\<^sub>p rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta>"
proof (cases "is_NegChecks b")
  case True
  then obtain X F G where b: "b = NegChecks X F G" by (cases b) moura+
  hence "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p b = set G" "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = set (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta>)"
    by simp_all
  thus ?thesis using t subst_apply_pairs_pset_subst[of G] by blast
next
  case False
  hence "setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b)) \<delta>"
    using setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst' bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegChecks by fastforce
  thus ?thesis using t by blast
qed

lemma setops\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes "bvars\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}"
  shows "setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms
proof (induction S)
  case (Cons a S)
  have "bvars\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}" and *: "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) \<inter> subst_domain \<theta> = {}"
    using Cons.prems by auto
  hence IH: "setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
    using Cons.IH by auto
  show ?case
    using setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[OF *] IH unfolding setops\<^sub>s\<^sub>s\<^sub>t_def
    by (auto simp add: subst_apply_stateful_strand_def)
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_subst':
  fixes p::"('a,'b) term \<times> ('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes "p \<in> setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  shows "\<exists>s \<in> setops\<^sub>s\<^sub>s\<^sub>t S. \<exists>X. set X \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t S \<and> p = s \<cdot>\<^sub>p rm_vars (set X) \<delta>"
using assms
proof (induction S)
  case (Cons a S)
  note 0 = setops\<^sub>s\<^sub>s\<^sub>t_cons[of a S] bvars\<^sub>s\<^sub>s\<^sub>t_Cons[of a S]
  note 1 = setops\<^sub>s\<^sub>s\<^sub>t_cons[of "a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>"] subst_sst_cons[of a S \<delta>]
  have "p \<in> setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>) \<or> p \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)" using Cons.prems 1 by auto
  thus ?case
  proof
    assume *: "p \<in> setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    show ?thesis using setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst''[OF *] 0 by blast
  next
    assume *: "p \<in> setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    show ?thesis using Cons.IH[OF *] 0 by blast
  qed
qed simp


subsection \<open>Stateful Constraint Semantics\<close>
context intruder_model
begin

definition negchecks_model where
  "negchecks_model (\<I>::('a,'b) subst) (D::('a,'b) dbstate) X F G \<equiv>
      (\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> 
              (\<exists>(t,s) \<in> set F. t \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> s \<cdot> \<delta> \<circ>\<^sub>s \<I>) \<or>
              (\<exists>(t,s) \<in> set G. (t,s) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> D))"

fun strand_sem_stateful::
  "('fun,'var) terms \<Rightarrow> ('fun,'var) dbstate \<Rightarrow> ('fun,'var) stateful_strand \<Rightarrow> ('fun,'var) subst \<Rightarrow> bool"
  ("\<lbrakk>_; _; _\<rbrakk>\<^sub>s")
where
  "\<lbrakk>M; D; []\<rbrakk>\<^sub>s = (\<lambda>\<I>. True)"
| "\<lbrakk>M; D; Send ts#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. (\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<I>) \<and> \<lbrakk>M; D; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; Receive ts#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. \<lbrakk>(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> M; D; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; Equality _ t t'#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. t \<cdot> \<I> = t' \<cdot> \<I> \<and> \<lbrakk>M; D; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; Insert t s#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. \<lbrakk>M; insert ((t,s) \<cdot>\<^sub>p \<I>) D; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; Delete t s#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. \<lbrakk>M; D - {(t,s) \<cdot>\<^sub>p \<I>}; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; InSet _ t s#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. (t,s) \<cdot>\<^sub>p \<I> \<in> D \<and> \<lbrakk>M; D; S\<rbrakk>\<^sub>s \<I>)"
| "\<lbrakk>M; D; NegChecks X F F'#S\<rbrakk>\<^sub>s = (\<lambda>\<I>. negchecks_model \<I> D X F F' \<and> \<lbrakk>M; D; S\<rbrakk>\<^sub>s \<I>)"


lemmas strand_sem_stateful_induct =
  strand_sem_stateful.induct[case_names Nil ConsSnd ConsRcv ConsEq
                                        ConsIns ConsDel ConsIn ConsNegChecks]

abbreviation constr_sem_stateful (infix "\<Turnstile>\<^sub>s" 91) where "\<I> \<Turnstile>\<^sub>s A \<equiv> \<lbrakk>{}; {}; A\<rbrakk>\<^sub>s \<I>"

lemma stateful_strand_sem_NegChecks_no_bvars:
  "\<lbrakk>M; D; [\<langle>t not in s\<rangle>]\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> (t \<cdot> \<I>, s \<cdot> \<I>) \<notin> D"
  "\<lbrakk>M; D; [\<langle>t != s\<rangle>]\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> t \<cdot> \<I> \<noteq> s \<cdot> \<I>"
by (simp_all add: negchecks_model_def empty_dom_iff_empty_subst)

lemma strand_sem_ik_mono_stateful:
  "\<lbrakk>M; D; A\<rbrakk>\<^sub>s \<I> \<Longrightarrow> \<lbrakk>M \<union> M'; D; A\<rbrakk>\<^sub>s \<I>"
proof (induction A arbitrary: M M' D rule: strand_sem_stateful.induct)
  case (2 M D ts S)
  hence "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<I>" "\<lbrakk>M \<union> M'; D; S\<rbrakk>\<^sub>s \<I>" by auto
  thus ?case
    using ideduct_mono[of M _ "M \<union> M'"] strand_sem_stateful.simps(2)[of "M \<union> M'" D ts S]
    by fastforce
next
  case (3 M D ts S)
  hence "\<lbrakk>((set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> M) \<union> M'; D; S\<rbrakk>\<^sub>s \<I>" by simp
  hence "\<lbrakk>(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (M \<union> M'); D; S\<rbrakk>\<^sub>s \<I>" by (metis Un_assoc)
  thus ?case by simp
qed simp_all

lemma strand_sem_append_stateful:
  "\<lbrakk>M; D; A@B\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> \<lbrakk>M; D; A\<rbrakk>\<^sub>s \<I> \<and> \<lbrakk>M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>); dbupd\<^sub>s\<^sub>s\<^sub>t A \<I> D; B\<rbrakk>\<^sub>s \<I>"
  (is "?P \<longleftrightarrow> ?Q \<and> ?R")
proof -
  have 1: "?P \<Longrightarrow> ?Q" by (induct A rule: strand_sem_stateful.induct) auto

  have 2: "?P \<Longrightarrow> ?R"
  proof (induction A arbitrary: M D B)
    case (Cons a A) thus ?case
    proof (cases a)
      case (Receive ts)
      have "(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)) = M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
           "dbupd\<^sub>s\<^sub>s\<^sub>t A \<I> D = dbupd\<^sub>s\<^sub>s\<^sub>t (a#A) \<I> D"
        using Receive by (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
      thus ?thesis
        using Cons Receive
        by (metis (no_types, lifting) Un_assoc append_Cons strand_sem_stateful.simps(3))
    qed (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
  qed (simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

  have 3: "?Q \<Longrightarrow> ?R \<Longrightarrow> ?P"
  proof (induction A arbitrary: M D)
    case (Cons a A) thus ?case
    proof (cases a)
      case (Receive ts)
      have "(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)) = M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
           "dbupd\<^sub>s\<^sub>s\<^sub>t A \<I> D = dbupd\<^sub>s\<^sub>s\<^sub>t (a#A) \<I> D"
        using Receive by (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
      thus ?thesis
        using Cons Receive
        by (metis (no_types, lifting) Un_assoc append_Cons strand_sem_stateful.simps(3))
    qed (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
  qed (simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)

  show ?thesis by (metis 1 2 3)
qed

lemma negchecks_model_db_subset:
  fixes F F'::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "D' \<subseteq> D"
  and "negchecks_model \<I> D X F F'"
  shows "negchecks_model \<I> D' X F F'"
proof -
  have "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> D'"
    when "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> D"
    for \<delta>::"('a,'b) subst"
    using that assms(1) by blast
  thus ?thesis using assms(2) unfolding negchecks_model_def by meson
qed

lemma negchecks_model_db_supset:
  fixes F F'::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "D' \<subseteq> D"
    and "\<forall>f \<in> set F'. \<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> D - D'"
    and "negchecks_model \<I> D' X F F'"
  shows "negchecks_model \<I> D X F F'"
proof -
  have "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> D"
    when "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> D'" "subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"
    for \<delta>::"('a,'b) subst"
    using that assms(1,2) by blast
  thus ?thesis using assms(3) unfolding negchecks_model_def by meson
qed

lemma negchecks_model_subst:
  fixes F F'::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
  shows "negchecks_model (\<delta> \<circ>\<^sub>s \<theta>) D X F F' \<longleftrightarrow> negchecks_model \<theta> D X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
proof -
  have 0: "\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) = \<delta> \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<theta>)"
    when \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)" for \<sigma>
    by (metis (no_types, lifting) \<sigma> subst_compose_assoc assms(1) inf_sup_aci(1)
            subst_comp_eq_if_disjoint_vars sup_inf_absorb range_vars_alt_def)

  { fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "\<exists>(s,t) \<in> set F. s \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<noteq> t \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>))"
    obtain f where f: "f \<in> set F" "fst f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)"
      using * unfolding case_prod_unfold by (induct F) auto
    hence "(fst f \<cdot> \<delta>) \<cdot> \<sigma> \<circ>\<^sub>s \<theta> \<noteq> (snd f \<cdot> \<delta>) \<cdot> \<sigma> \<circ>\<^sub>s \<theta>" using 0[OF \<sigma>] by simp
    moreover have "(fst f \<cdot> \<delta>, snd f \<cdot> \<delta>) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using f(1) by (auto simp add: subst_apply_pairs_def)
    ultimately have "\<exists>(s,t) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>). s \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>) \<noteq> t \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>)"
      using f(1) by fastforce
  } moreover {
    fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<notin> D"
    obtain f where f: "f \<in> set F'" "f \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<notin> D"
      using * by (induct F') auto
    hence "f \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s \<theta> \<notin> D" using 0[OF \<sigma>] by (metis subst_pair_compose)
    moreover have "f \<cdot>\<^sub>p \<delta> \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using f(1) by (auto simp add: subst_apply_pairs_def)
    ultimately have "\<exists>(s,t) \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>). (s,t) \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s \<theta> \<notin> D"
      using f(1) by (metis (no_types, lifting) case_prodI2)
  } moreover {
    fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "\<exists>(s,t) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>). s \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>) \<noteq> t \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>)"
    obtain f where f: "f \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)" "fst f \<cdot> \<sigma> \<circ>\<^sub>s \<theta> \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s \<theta>"
      using * by (induct F) auto
    then obtain g where g: "g \<in> set F" "f = g \<cdot>\<^sub>p \<delta>" by (auto simp add: subst_apply_pairs_def)
    have "fst g \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> snd g \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)"
      using f(2) g 0[OF \<sigma>] by (simp add: prod.case_eq_if)
    hence "\<exists>(s,t) \<in> set F. s \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<noteq> t \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>))"
      using g by fastforce
  } moreover {
    fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "\<exists>(s,t) \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>). (s,t) \<cdot>\<^sub>p (\<sigma> \<circ>\<^sub>s \<theta>) \<notin> D"
    obtain f where f: "f \<in> set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)" "f \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s \<theta> \<notin> D"
      using * by (induct F') auto
    then obtain g where g: "g \<in> set F'" "f = g \<cdot>\<^sub>p \<delta>" by (auto simp add: subst_apply_pairs_def)
    have "g \<cdot>\<^sub>p \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<notin> D"
      using f(2) g 0[OF \<sigma>] by (simp add: prod.case_eq_if)
    hence "\<exists>(s,t) \<in> set F'. (s,t) \<cdot>\<^sub>p (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<notin> D"
      using g by (metis (no_types, lifting) case_prodI2)
  } ultimately show ?thesis
      using assms unfolding negchecks_model_def by meson
qed

lemma strand_sem_subst_stateful:
  fixes \<delta>::"('fun,'var) subst"
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<longleftrightarrow> \<lbrakk>M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>"
proof
  note [simp] = subst_sst_cons[of _ _ \<delta>] subst_subst_compose[of _ \<delta> \<theta>]

  have "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
    when \<delta>: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
      and \<gamma>: "subst_domain \<gamma> = set X" "ground (subst_range \<gamma>)"
    for X and \<gamma>::"('fun,'var) subst"
    using \<delta> \<gamma> unfolding range_vars_alt_def by auto
  hence 0: "\<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
    when \<delta>: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
      and \<gamma>: "subst_domain \<gamma> = set X" "ground (subst_range \<gamma>)"
    for \<gamma> X
    by (metis \<delta> \<gamma> subst_comp_eq_if_disjoint_vars)

  show "\<lbrakk>M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<Longrightarrow> \<lbrakk>M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>" using assms
  proof (induction S arbitrary: M D rule: strand_sem_stateful_induct)
    case (ConsSnd M D ts S)
    hence "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<delta> \<cdot> \<theta>" and IH: "\<lbrakk>M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>" by auto
    hence "\<forall>t \<in> set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>). M \<turnstile> t \<cdot> \<theta>" by simp
    thus ?case using IH by simp
  next
    case (ConsRcv M D ts S)
    hence "\<lbrakk>(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<circ>\<^sub>s \<theta>) \<union> M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>" by simp
    hence "\<lbrakk>(set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>" by (metis list.set_map subst_comp_all) 
    thus ?case by simp
  next
    case (ConsNegChecks M D X F F' S)
    hence *: "\<lbrakk>M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta>" and **: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
      unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def negchecks_model_def by (force, auto)
    have "negchecks_model (\<delta> \<circ>\<^sub>s \<theta>) D X F F'" using ConsNegChecks by auto
    hence "negchecks_model \<theta> D X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using 0[OF **] negchecks_model_subst[OF **] by blast
    moreover have "rm_vars (set X) \<delta> = \<delta>" using ConsNegChecks.prems(2) by force
    ultimately show ?case using * by auto
  qed simp_all

  show "\<lbrakk>M; D; S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>s \<theta> \<Longrightarrow> \<lbrakk>M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" using assms
  proof (induction S arbitrary: M D rule: strand_sem_stateful_induct)
    case (ConsSnd M D ts S)
    hence "\<forall>t \<in> set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>). M \<turnstile> t \<cdot> \<theta>" and IH: "\<lbrakk>M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" by auto
    hence "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> \<delta> \<cdot> \<theta>" by simp
    thus ?case using IH by simp
  next
    case (ConsRcv M D ts S)
    hence "\<lbrakk>(set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" by simp
    hence "\<lbrakk>(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<circ>\<^sub>s \<theta>) \<union> M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" by (metis list.set_map subst_comp_all) 
    thus ?case by simp
  next
    case (ConsNegChecks M D X F F' S)
    have \<delta>: "rm_vars (set X) \<delta> = \<delta>" using ConsNegChecks.prems(2) by force
    hence *: "\<lbrakk>M; D; S\<rbrakk>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" and **: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
      using ConsNegChecks unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def negchecks_model_def by auto
    have "negchecks_model \<theta> D X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using ConsNegChecks.prems(1) \<delta> by (auto simp add: subst_compose_assoc negchecks_model_def)
    hence "negchecks_model (\<delta> \<circ>\<^sub>s \<theta>) D X F F'"
      using 0[OF **] negchecks_model_subst[OF **] by blast
    thus ?case using * by auto
  qed simp_all
qed

lemma strand_sem_receive_prepend_stateful:
  assumes "\<lbrakk>M; D; S\<rbrakk>\<^sub>s \<theta>"
    and "list_all is_Receive S'"
  shows "\<lbrakk>M; D; S@S'\<rbrakk>\<^sub>s \<theta>"
using assms(2)
proof (induction S' rule: List.rev_induct)
  case (snoc x S')
  hence "\<exists>t. x = receive\<langle>t\<rangle>" "\<lbrakk>M; D; S@S'\<rbrakk>\<^sub>s \<theta>"
    unfolding list_all_iff is_Receive_def by auto
  thus ?case using strand_sem_append_stateful[of M D "S@S'" "[x]" \<theta>] by auto
qed (simp add: assms(1))

lemma negchecks_model_model_swap:
  fixes I J::"('a,'b) subst"
  assumes "\<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G) - set X. I x = J x"
    and "negchecks_model I D X F G"
  shows "negchecks_model J D X F G"
proof -
  have 0: "\<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G). (\<delta> \<circ>\<^sub>s I) x = (\<delta> \<circ>\<^sub>s J) x"
    when "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
    for \<delta>::"('a,'b) subst"
    using that assms(1)
    by (metis DiffI ground_subst_range_empty_fv subst_comp_notin_dom_eq
              subst_ground_ident_compose(1))

  have 1: "s \<cdot> (\<delta> \<circ>\<^sub>s J) \<noteq> t \<cdot> (\<delta> \<circ>\<^sub>s J)"
    when "s \<cdot> (\<delta> \<circ>\<^sub>s I) \<noteq> t \<cdot> (\<delta> \<circ>\<^sub>s I)" "(s,t) \<in> set F"
         "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
    for \<delta>::"('a,'b) subst" and s t
    using that(1,2) 0[OF that(3,4)] term_subst_eq_conv[of _ "\<delta> \<circ>\<^sub>s I" "\<delta> \<circ>\<^sub>s J"]
          UnCI fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_inI(4,5)[OF that(2)]
    by metis

  have 2: "(s,t) \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s J) \<notin> D"
    when "(s,t) \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s I) \<notin> D" "(s,t) \<in> set G"
         "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
    for \<delta>::"('a,'b) subst" and s t
    using that(1,2) 0[OF that(3,4)] fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_inI(4,5)[of s t G]
          term_subst_eq_conv[of s "\<delta> \<circ>\<^sub>s I" "\<delta> \<circ>\<^sub>s J"]
          term_subst_eq_conv[of t "\<delta> \<circ>\<^sub>s I" "\<delta> \<circ>\<^sub>s J"]
    by simp

  have 3: "(\<exists>(s,t) \<in> set F. s \<cdot> \<delta> \<circ>\<^sub>s J \<noteq> t \<cdot> \<delta> \<circ>\<^sub>s J) \<or> (\<exists>(s,t) \<in> set G. (s, t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s J \<notin> D)"
    when "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
         "(\<exists>(s,t) \<in> set F. s \<cdot> \<delta> \<circ>\<^sub>s I \<noteq> t \<cdot> \<delta> \<circ>\<^sub>s I) \<or> (\<exists>(s,t) \<in> set G. (s, t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s I \<notin> D)"
    for \<delta>::"('a,'b) subst"
    using 1[OF _ _ that(1,2)] 2[OF _ _ that(1,2)] that(3) by blast
  thus ?thesis
    using assms(2) unfolding negchecks_model_def by simp
qed

lemma strand_sem_model_swap:
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>s\<^sub>t S. I x = J x"
    and "\<lbrakk>M; D; S\<rbrakk>\<^sub>s I"
  shows "\<lbrakk>M; D; S\<rbrakk>\<^sub>s J"
using assms(2,1)
proof (induction S arbitrary: M D rule: strand_sem_stateful_induct)
  case (ConsSnd M D ts S)
  hence *: "\<lbrakk>M; D; S\<rbrakk>\<^sub>s J" "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> I" "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts). I x = J x"
    by (fastforce, fastforce, fastforce)

  have "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> J"
    using *(2,3) term_subst_eq_conv[of _ I J]
    by (metis fv_subset subsetD)
  thus ?case using *(1) by auto
next
  case (ConsRcv M D ts S)
  hence *: "\<lbrakk>(set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> M; D; S\<rbrakk>\<^sub>s J" "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts). I x = J x"
    by (fastforce, fastforce)

  have "set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t I = set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t J"
    using *(2) term_subst_eq_conv[of _ I J]
    by (meson fv_subset image_cong subsetD)
  thus ?case using *(1) by simp
next
  case (ConsEq M D ac t t' S) thus ?case
    using term_subst_eq_conv[of t I J] term_subst_eq_conv[of t' I J] by force
next
  case (ConsIns M D t s S) thus ?case
    using term_subst_eq_conv[of t I J] term_subst_eq_conv[of s I J] by force
next
  case (ConsDel M D t s S) thus ?case
    using term_subst_eq_conv[of t I J] term_subst_eq_conv[of s I J] by force
next
  case (ConsIn M D uv t s S) thus ?case
    using term_subst_eq_conv[of t I J] term_subst_eq_conv[of s I J] by force
next
  case (ConsNegChecks M D X F F' S)
  hence "\<lbrakk>M; D; S\<rbrakk>\<^sub>s J" "negchecks_model I D X F F'" "\<forall>x\<in>fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' - set X. I x = J x"
    by (fastforce, fastforce, fastforce)
  thus ?case using negchecks_model_model_swap[of F F' X I J D] by fastforce
qed simp

lemma strand_sem_receive_send_append:
  assumes A: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
  shows "\<lbrakk>M; D; A@[receive\<langle>[t]\<rangle>,send\<langle>[t]\<rangle>]\<rbrakk>\<^sub>s I"
proof -
  have "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (A@[receive\<langle>[t]\<rangle>]) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<turnstile> t \<cdot> I"
    using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of t "A@[receive\<langle>[t]\<rangle>]"] by auto
  thus ?thesis
    using A strand_sem_append_stateful[of M D A "[receive\<langle>[t]\<rangle>]" I]
          strand_sem_append_stateful[of M D "A@[receive\<langle>[t]\<rangle>]" "[send\<langle>[t]\<rangle>]" I]
    by force
qed

lemma strand_sem_stateful_if_no_send_or_check:
  assumes A: "list_all (\<lambda>a. \<not>is_Send a \<and> \<not>is_Check_or_Assignment a) A"
  shows "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
using A
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  hence IH: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I" and a: "\<not>is_Send a" "\<not>is_Check_or_Assignment a" by auto
  from a have "\<lbrakk>M; D; [a]\<rbrakk>\<^sub>s I" for M D by (cases a) auto
  thus ?case using IH strand_sem_append_stateful[of M D A "[a]" I] by blast
qed simp

lemma strand_sem_stateful_if_sends_deduct:
  assumes "list_all is_Send A"
    and "\<forall>ts. send\<langle>ts\<rangle> \<in> set A \<longrightarrow> (\<forall>t \<in> set ts. M \<turnstile> t \<cdot> I)"
  shows "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
using assms
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  hence IH: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I" by auto
  obtain ts where a: "a = send\<langle>ts\<rangle>" "\<forall>t \<in> set ts. M \<turnstile> t \<cdot> I" using snoc.prems by (cases a) auto

  have "\<lbrakk>M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I); D; [a]\<rbrakk>\<^sub>s I" for D
    using ideduct_mono[of M _ "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"] a by auto
  thus ?case using IH strand_sem_append_stateful[of M D A "[a]" I] by blast
qed simp

lemma strand_sem_stateful_if_checks:
  assumes "list_all is_Check_or_Assignment A"
    and "\<forall>ac t s. \<langle>ac: t \<doteq> s\<rangle> \<in> set A \<longrightarrow> t \<cdot> I = s \<cdot> I"
    and "\<forall>ac t s. \<langle>ac: t \<in> s\<rangle> \<in> set A \<longrightarrow> (t \<cdot> I, s \<cdot> I) \<in> D"
    and "\<forall>X F G. \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set A \<longrightarrow> negchecks_model I D X F G"
  shows "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
using assms
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  hence IH: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I" and a: "is_Check_or_Assignment a" by auto

  have 0: "dbupd\<^sub>s\<^sub>s\<^sub>t A I D = D"
    using snoc.prems(1) dbupd\<^sub>s\<^sub>s\<^sub>t_no_upd[of A I D] unfolding list_all_iff by auto

  have "\<lbrakk>M; D; [a]\<rbrakk>\<^sub>s I" for M using a snoc.prems(2,3,4) by (cases a) auto
  thus ?case using IH strand_sem_append_stateful[of M D A "[a]" I] unfolding 0 by blast
qed simp

lemma strand_sem_stateful_sends_deduct:
  assumes A: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
    and ts: "send\<langle>ts\<rangle> \<in> set A"
    and t: "t \<in> set ts"
  shows "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<turnstile> t \<cdot> I"
using A ts
proof (induction A arbitrary: M D rule: List.rev_induct)
  case (snoc a A)
  have 0: "\<lbrakk>M; D; A\<rbrakk>\<^sub>s I"
    using strand_sem_append_stateful snoc.prems(1) by fast

  have 1: "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<subseteq> M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (A@[a]) \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
    by auto

  have 2: "M \<union> (ik\<^sub>s\<^sub>s\<^sub>t (A@[send\<langle>ts\<rangle>]) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = M \<union> (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
    using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ A] in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ "A@[send\<langle>ts\<rangle>]"] by fastforce

  show ?case
  proof (cases "send\<langle>ts\<rangle> \<in> set A")
    case True show ?thesis by (rule ideduct_mono[OF snoc.IH[OF 0 True] 1])
  next
    case False
    hence a: "a = send\<langle>ts\<rangle>" using snoc.prems(2) by force
    show ?thesis
      using strand_sem_append_stateful[of M D A "[a]" I] snoc.prems(1) t
      unfolding a 2 by auto
  qed
qed simp

end


subsection \<open>Well-Formedness Lemmata\<close>
lemma wfvarsocc\<^sub>s\<^sub>s\<^sub>t_subset_wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t[simp]:
  "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
by (induction S)
   (auto simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def
         split: stateful_strand_step.split poscheckvariant.split)

lemma wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_append: "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t (S@S') = wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S'"
by (simp add: wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)

lemma wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_union[simp]:
  "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (S@T) = wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t T"
by (simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_singleton:
  "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t [s] = wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s"
by (simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma ik\<^sub>s\<^sub>s\<^sub>t_fv_subset_wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t[simp]:
  "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>s\<^sub>t S) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of _ S] unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by force

lemma wf\<^sub>s\<^sub>s\<^sub>t_prefix[dest]: "wf'\<^sub>s\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t V S"
by (induct S rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct) auto

lemma wf\<^sub>s\<^sub>s\<^sub>t_vars_mono: "wf'\<^sub>s\<^sub>s\<^sub>t V S \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> W) S"
proof (induction S arbitrary: V)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Send ts)
    have "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> W \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts)) S"
      using Cons.prems(1) Cons.IH Send by (metis sup_assoc sup_commute wf'\<^sub>s\<^sub>s\<^sub>t.simps(3))
    thus ?thesis by (simp add: Send)
  next
    case (Equality a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> W) S" "fv t' \<subseteq> V \<union> W" using Equality Cons.prems(1) Cons.IH by auto
      thus ?thesis using Equality Assign by (simp add: sup_commute sup_left_commute)
    next
      case Check thus ?thesis using Equality Cons by auto
    qed
  next
    case (InSet a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv t' \<union> W) S" using InSet Cons.prems(1) Cons.IH by auto
      thus ?thesis using InSet Assign by (simp add: sup_commute sup_left_commute)
    next
      case Check thus ?thesis using InSet Cons by auto
    qed
  qed auto
qed simp

lemma wf\<^sub>s\<^sub>s\<^sub>tI[intro]: "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<subseteq> V \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t V S"
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Send ts)
    hence "wf'\<^sub>s\<^sub>s\<^sub>t V S" "V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts) = V"
      using Cons
      unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def
      by auto
    thus ?thesis using Send by simp
  next
    case (Equality a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t V S" "fv t' \<subseteq> V"
        using Equality Cons 
        unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def
        by auto
      thus ?thesis using wf\<^sub>s\<^sub>s\<^sub>t_vars_mono Equality Assign by simp
    next
      case Check
      thus ?thesis
        using Equality Cons
        unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def
        by auto
    qed
  next
    case (InSet a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t V S" "fv t \<union> fv t' \<subseteq> V"
        using InSet Cons
        unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def
        by auto
      thus ?thesis using wf\<^sub>s\<^sub>s\<^sub>t_vars_mono InSet Assign by (simp add: Un_assoc) 
    next
      case Check
      thus ?thesis
        using InSet Cons
        unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def
        by auto
    qed
  qed (simp_all add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)
qed (simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>tI'[intro]:
  assumes "\<Union>((\<lambda>x. case x of
            Receive ts \<Rightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set ts)
          | Equality Assign _ t' \<Rightarrow> fv t'
          | Insert t t' \<Rightarrow> fv t \<union> fv t'
          | _ \<Rightarrow> {}) ` set S) \<subseteq> V"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t V S"
using assms
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Equality a t t')
    thus ?thesis using Cons by (cases a) (auto simp add: wf\<^sub>s\<^sub>s\<^sub>t_vars_mono)
  next
    case (InSet a t t')
    thus ?thesis using Cons by (cases a) (auto simp add: wf\<^sub>s\<^sub>s\<^sub>t_vars_mono Un_assoc)
  qed (simp_all add: wf\<^sub>s\<^sub>s\<^sub>t_vars_mono)
qed simp

lemma wf\<^sub>s\<^sub>s\<^sub>t_append_exec: "wf'\<^sub>s\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'"
proof (induction S arbitrary: V)
  case (Cons x S V) thus ?case
  proof (cases x)
    case (Send ts)
    hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'" using Cons.prems Cons.IH by simp
    thus ?thesis using Send unfolding wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by (auto simp add: sup_assoc)
  next
    case (Equality a t t') show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'" using Equality Cons.prems Cons.IH by auto
      thus ?thesis using Equality Assign unfolding wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by (auto simp add: sup_assoc)
    next
      case Check
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'" using Equality Cons.prems Cons.IH by auto
      thus ?thesis using Equality Check unfolding wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by (auto simp add: sup_assoc)
    qed
  next
    case (InSet a t t') show ?thesis
    proof (cases a)
      case Assign
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv t' \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'" using InSet Cons.prems Cons.IH by auto
      thus ?thesis using InSet Assign unfolding wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by (auto simp add: sup_assoc)
    next
      case Check
      hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) S'" using InSet Cons.prems Cons.IH by auto
      thus ?thesis using InSet Check unfolding wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by (auto simp add: sup_assoc)
    qed
  qed (auto simp add: wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)
qed (simp add: wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_append:
  "wf'\<^sub>s\<^sub>s\<^sub>t X S \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t Y T \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> Y) (S@T)"
proof (induction X S rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
  case 1 thus ?case by (metis wf\<^sub>s\<^sub>s\<^sub>t_vars_mono Un_commute append_Nil)
next
  case 3 thus ?case by (metis append_Cons Un_commute Un_assoc wf'\<^sub>s\<^sub>s\<^sub>t.simps(3))
next
  case (4 V t t' S)
  hence *: "fv t' \<subseteq> V" and "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> Y) (S @ T)" by simp_all
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> Y \<union> fv t) (S @ T)" by (metis Un_commute Un_assoc)
  thus ?case using * by auto
next
  case (8 V t t' S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv t' \<union> Y) (S @ T)" by simp_all
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> Y \<union> fv t \<union> fv t') (S @ T)" by (metis Un_commute Un_assoc)
  thus ?case by auto
qed auto

lemma wf\<^sub>s\<^sub>s\<^sub>t_append_suffix:
  "wf'\<^sub>s\<^sub>s\<^sub>t V S \<Longrightarrow> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> V \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t V (S@S')"
proof (induction V S rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
  case (2 V ts S)
  hence *: "fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> V" "wf'\<^sub>s\<^sub>s\<^sub>t V S" by simp_all
  hence "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> V"
    using "2.prems"(2) unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  thus ?case using "2.IH" * by simp
next
  case (3 V ts S)
  hence *: "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts)) S" by simp_all
  hence "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts))"
    using "3.prems"(2) unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
  thus ?case using "3.IH" * by simp
next
  case (4 V t t' S)
  hence *: "fv t' \<subseteq> V" "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t) S" by simp_all
  moreover have "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (\<langle>t := t'\<rangle>) = fv t \<union> fv t'"
    by simp
  moreover have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (\<langle>t := t'\<rangle>#S) = fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
  ultimately have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> (V \<union> fv t)"
    using "4.prems"(2) by blast
  thus ?case using "4.IH" * by simp
next
  case (6 V t t' S)
  hence *: "fv t \<union> fv t' \<subseteq> V" "wf'\<^sub>s\<^sub>s\<^sub>t V S" by simp_all
  moreover have "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (insert\<langle>t,t'\<rangle>) = fv t \<union> fv t'"
    by simp
  moreover have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (insert\<langle>t,t'\<rangle>#S) = fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
  ultimately have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> V"
    using "6.prems"(2) by blast
  thus ?case using "6.IH" * by simp
next
  case (8 V t t' S)
  hence *: "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv t') S" by simp_all
  moreover have "vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (select\<langle>t,t'\<rangle>) = fv t \<union> fv t'"
    by simp
  moreover have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (select\<langle>t,t'\<rangle>#S) = fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
  ultimately have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S \<union> (V \<union> fv t \<union> fv t')"
    using "8.prems"(2) by blast
  thus ?case using "8.IH" * by simp
qed (simp_all add: wf\<^sub>s\<^sub>s\<^sub>tI wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_append_suffix':
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t V S"
    and "\<Union>((\<lambda>x. case x of
            Receive ts \<Rightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set ts)
          | Equality Assign _ t' \<Rightarrow> fv t'
          | Insert t t' \<Rightarrow> fv t \<union> fv t'
          | _ \<Rightarrow> {}) ` set S') \<subseteq> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S \<union> V"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t V (S@S')"
using assms
by (induction V S rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
   (auto simp add: wf\<^sub>s\<^sub>s\<^sub>tI' wf\<^sub>s\<^sub>s\<^sub>t_vars_mono wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_subst_apply:
  "wf'\<^sub>s\<^sub>s\<^sub>t V S \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
proof (induction S arbitrary: V rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
  case (2 V ts S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t V S" "fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> V" by simp_all
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" "fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
    using "2.IH" subst_apply_fv_subset by (simp, force)
  thus ?case by (simp add: subst_apply_stateful_strand_def)
next
  case (3 V ts S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts)) S" by simp
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts)))) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" using "3.IH" by metis
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    using  subst_apply_fv_unfold_set[of \<delta> ts] by fastforce
  thus ?case by (simp add: subst_apply_stateful_strand_def)
next
  case (4 V t t' S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t) S" "fv t' \<subseteq> V" by auto
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t))) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" and *: "fv (t' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
    using "4.IH" subst_apply_fv_subset by force+
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" by (metis subst_apply_fv_union)
  thus ?case using * by (simp add: subst_apply_stateful_strand_def)
next
  case (6 V t t' S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t V S" "fv t \<union> fv t' \<subseteq> V" by auto
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" "fv (t \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)" "fv (t' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
    using "6.IH" subst_apply_fv_subset by force+
  thus ?case by (simp add: sup_assoc subst_apply_stateful_strand_def)
next
  case (8 V t t' S)
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> fv t \<union> fv t') S" by auto
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t \<union> fv t'))) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    using "8.IH" subst_apply_fv_subset by force
  hence "wf'\<^sub>s\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)) (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" by (metis subst_apply_fv_union)
  thus ?case by (simp add: subst_apply_stateful_strand_def)
qed (auto simp add: subst_apply_stateful_strand_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_induct[consumes 1,
                  case_names Nil ConsSnd ConsRcv ConsEq ConsEq2 ConsIn ConsIns ConsDel
                             ConsNegChecks]:
  fixes S::"('a,'b) stateful_strand"
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t V S"
          "P []"
          "\<And>ts S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Send ts])"
          "\<And>ts S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S; fv\<^sub>s\<^sub>e\<^sub>t (set ts) \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> P (S@[Receive ts])"
          "\<And>t t' S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S; fv t' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> P (S@[Equality Assign t t'])"
          "\<And>t t' S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Equality Check t t'])"
          "\<And>ac t t' S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[InSet ac t t'])"
          "\<And>t t' S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S; fv t \<union> fv t' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> P (S@[Insert t t'])"
          "\<And>t t' S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Delete t t'])"
          "\<And>X F G S. \<lbrakk>wf'\<^sub>s\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[NegChecks X F G])"
  shows "P S"
using assms
proof (induction S rule: List.rev_induct)
  case (snoc x S)
  hence *: "wf'\<^sub>s\<^sub>s\<^sub>t V S" "wf'\<^sub>s\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S) [x]"
    by (metis wf\<^sub>s\<^sub>s\<^sub>t_prefix, metis wf\<^sub>s\<^sub>s\<^sub>t_append_exec)
  have IH: "P S" using snoc.IH[OF *(1)] snoc.prems by auto
  note ** = snoc.prems(3-)[OF *(1) IH] *(2)
  show ?case
  proof (cases x)
    case (Send ts) thus ?thesis using **(1) by blast
  next
    case (Receive ts) thus ?thesis using **(2,9) by simp
  next
    case (Equality ac t t') thus ?thesis using **(3,4,9) by (cases ac) auto
  next
    case (Insert t t') thus ?thesis using **(6,9) by force
  next
    case (Delete t t') thus ?thesis using **(7) by presburger
  next
    case (NegChecks X F G) thus ?thesis using **(8) by presburger
  next
    case (InSet ac t t') thus ?thesis using **(5) by (cases ac) auto
  qed
qed simp

lemma wf\<^sub>s\<^sub>s\<^sub>t_strand_first_Send_var_split:
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t {} S" "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v"
  shows "\<exists>S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. \<not>(\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e. t \<cdot> \<I> \<sqsubseteq> \<I> w) \<and> (
                    (\<exists>ts. S = S\<^sub>p\<^sub>r\<^sub>e@send\<langle>ts\<rangle>#S\<^sub>s\<^sub>u\<^sub>f \<and> t \<cdot> \<I> \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<or>
                    (\<exists>s u. S = S\<^sub>p\<^sub>r\<^sub>e@\<langle>assign: s \<doteq> u\<rangle>#S\<^sub>s\<^sub>u\<^sub>f \<and> t \<cdot> \<I> \<sqsubseteq> s \<cdot> \<I> \<and> \<not>(t \<cdot> \<I> \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t \<I> ` fv u)) \<or>
                    (\<exists>s u. S = S\<^sub>p\<^sub>r\<^sub>e@\<langle>assign: s \<in> u\<rangle>#S\<^sub>s\<^sub>u\<^sub>f \<and> (t \<cdot> \<I> \<sqsubseteq> s \<cdot> \<I> \<or> t \<cdot> \<I> \<sqsubseteq> u \<cdot> \<I>)))"
    (is "\<exists>S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. ?P S\<^sub>p\<^sub>r\<^sub>e \<and> ?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f")
using assms
proof (induction S rule: wf\<^sub>s\<^sub>s\<^sub>t_induct)
  case (ConsSnd ts' S) show ?case
  proof (cases "\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> w")
    case True
    then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
      using ConsSnd.IH by moura
    thus ?thesis by fastforce
  next
    case False
    then obtain v where v: "v \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts')" "t \<cdot> \<I> \<sqsubseteq> \<I> v"
      using ConsSnd.prems unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
    then obtain t' where t': "t' \<in> set ts'" "v \<in> fv t'" by auto
    have "t \<cdot> \<I> \<sqsubseteq> t' \<cdot> \<I>"
      using v(2) t'(2) subst_mono[of "Var v" t' \<I>] vars_iff_subtermeq[of v] term.order_trans
      by auto
    hence "t \<cdot> \<I> \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using v(1) t'(1) by blast
    thus ?thesis using False v by blast
  qed
next
  case (ConsRcv t' S)
  have "fv\<^sub>s\<^sub>e\<^sub>t (set t') \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    using ConsRcv.hyps wfvarsocc\<^sub>s\<^sub>s\<^sub>t_subset_wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t[of S] by blast
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v"
    using ConsRcv.prems unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
    using ConsRcv.IH by moura
  thus ?case by fastforce
next
  case (ConsEq s s' S)
  have *: "fv s' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    using ConsEq.hyps wfvarsocc\<^sub>s\<^sub>s\<^sub>t_subset_wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t[of S] by blast
  show ?case
  proof (cases "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v")
    case True
    then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
      using ConsEq.IH by moura
    thus ?thesis by fastforce
  next
    case False
    then obtain v where "v \<in> fv s" "t \<cdot> \<I> \<sqsubseteq> \<I> v" and **: "fv s' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
      using ConsEq.prems * unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
    hence "t \<cdot> \<I> \<sqsubseteq> s \<cdot> \<I>"
      using vars_iff_subtermeq[of v s] subst_mono[of "Var v" s \<I>] term.order_trans by auto
    thus ?thesis using False ** by fastforce
  qed
next
  case (ConsEq2 s s' S)
  have "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (S@[Equality Check s s']) = wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by auto
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v" using ConsEq2.prems by metis
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f" using ConsEq2.IH by moura
  thus ?case by fastforce
next
  case (ConsNegChecks X F G S)
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v" unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by simp
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f" using ConsNegChecks.IH by moura
  thus ?case by fastforce
next
  case (ConsIn ac s s' S)
  show ?case
  proof (cases "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v")
    case True
    then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
      using ConsIn.IH by moura
    thus ?thesis by fastforce
  next
    case False
    hence ac: "ac = assign" using ConsIn.prems unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by (cases ac) auto
    obtain v where "v \<in> fv s \<union> fv s'" "t \<cdot> \<I> \<sqsubseteq> \<I> v"
        using ConsIn.prems False unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def ac by auto
    hence *: "t \<cdot> \<I> \<sqsubseteq> s \<cdot> \<I> \<or> t \<cdot> \<I> \<sqsubseteq> s' \<cdot> \<I>"
      using vars_iff_subtermeq[of v s] vars_iff_subtermeq[of v s']
            subst_mono[of "Var v" s \<I>] subst_mono[of "Var v" s' \<I>] term.order_trans
      by auto
    show ?thesis using * False unfolding ac by fast
  qed
next
  case (ConsIns s s' S)
  have "fv s \<union> fv s' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S"
    using ConsIns.hyps wfvarsocc\<^sub>s\<^sub>s\<^sub>t_subset_wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t[of S] by blast
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v"
      using ConsIns.prems unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by fastforce
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f" using ConsIns.IH by moura
  thus ?case by fastforce
next
  case (ConsDel s s' S)
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v" unfolding wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by simp
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f" using ConsDel.IH by moura
  thus ?case by fastforce
qed (simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_vars_mono': "wf'\<^sub>s\<^sub>s\<^sub>t V S \<Longrightarrow> V \<subseteq> W \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t W S"
by (metis Diff_partition wf\<^sub>s\<^sub>s\<^sub>t_vars_mono)

lemma wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_receives_only_eq:
  assumes "list_all is_Receive S"
  shows "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S = fv\<^sub>s\<^sub>s\<^sub>t S"
using assms
proof (induction S)
  case (Cons a A)
  obtain ts where a: "a = receive\<langle>ts\<rangle>" using Cons.prems by (cases a) auto
  have IH: "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t A = fv\<^sub>s\<^sub>s\<^sub>t A" using Cons.prems Cons.IH by simp
  show ?case using IH unfolding a wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by simp
qed (simp add: wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def)

lemma wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_receives_only_empty:
  assumes "list_all is_Receive S"
  shows "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S = {}"
using assms
proof (induction S)
  case (Cons a A)
  obtain ts where a: "a = receive\<langle>ts\<rangle>" using Cons.prems by (cases a) auto
  have IH: "wfvarsoccs\<^sub>s\<^sub>s\<^sub>t A = {}" using Cons.prems Cons.IH by simp
  show ?case using IH unfolding a wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def by simp
qed (simp add: wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)

lemma wf\<^sub>s\<^sub>s\<^sub>t_sends_only:
  assumes "list_all is_Send S"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t V S"
using assms
proof (induction S arbitrary: V)
  case (Cons s S) thus ?case by (cases s) auto
qed simp

lemma wf\<^sub>s\<^sub>s\<^sub>t_sends_only_prepend:
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t V S"
    and "list_all is_Send S'"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t V (S'@S)"
using wf\<^sub>s\<^sub>s\<^sub>t_append[OF wf\<^sub>s\<^sub>s\<^sub>t_sends_only[OF assms(2), of "{}"] assms(1)] by simp

lemma wf\<^sub>s\<^sub>s\<^sub>t_receives_only_fv_subset:
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t V S"
    and "list_all is_Receive S"
  shows "fv\<^sub>s\<^sub>s\<^sub>t S \<subseteq> V"
using assms
proof (induction rule: wf\<^sub>s\<^sub>s\<^sub>t_induct)
  case (ConsRcv ts S) thus ?case using wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_receives_only_empty[of S] by auto
qed auto

lemma wf\<^sub>s\<^sub>s\<^sub>t_append_suffix'':
  assumes "wf'\<^sub>s\<^sub>s\<^sub>t V S"
    and "wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t S' \<subseteq> wfvarsoccs\<^sub>s\<^sub>s\<^sub>t S \<union> V"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t V (S@S')"
using assms
by (induction V S rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
   (auto simp add: wf\<^sub>s\<^sub>s\<^sub>tI' wf\<^sub>s\<^sub>s\<^sub>t_vars_mono wfvarsoccs\<^sub>s\<^sub>s\<^sub>t_def)


end
