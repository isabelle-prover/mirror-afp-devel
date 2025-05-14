(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "From regular expressions to nondeterministic automata with epsilon"

theory RegExp2NAe
imports "Regular-Sets.Regular_Exp" NAe  "HOL-ex.Sketch_and_Explore" 
begin

type_synonym 'a bitsNAe = "('a,bool list)nae"

definition
 epsilon :: "'a bitsNAe" where
"epsilon = ([],\<lambda>a s. {}, \<lambda>s. s=[])"

definition
"atom"  :: "'a \<Rightarrow> 'a bitsNAe" where
"atom a = ([True],
            \<lambda>b s. if s=[True] \<and> b=Some a then {[False]} else {},
            \<lambda>s. s=[False])"

definition
 or :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"or = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {True#ql,False#qr} else {}
          | left#s \<Rightarrow> if left then True ## dl a s
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> if left then fl s else fr s))"

definition
 conc :: "'a bitsNAe \<Rightarrow> 'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"conc = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left then (True ## dl a s) \<union>
                                   (if fl s \<and> a=None then {False#qr} else {})
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> \<not>left \<and> fr s))"

definition
 star :: "'a bitsNAe \<Rightarrow> 'a bitsNAe" where
"star = (\<lambda>(q,d,f).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> if a=None then {True#q} else {}
          | left#s \<Rightarrow> if left then (True ## d a s) \<union>
                                   (if f s \<and> a=None then {True#q} else {})
                              else {},
    \<lambda>s. case s of [] \<Rightarrow> True | left#s \<Rightarrow> left \<and> f s))"

primrec rexp2nae :: "'a rexp \<Rightarrow> 'a bitsNAe" where
"rexp2nae Zero       = ([], \<lambda>a s. {}, \<lambda>s. False)" |
"rexp2nae One        = epsilon" |
"rexp2nae(Atom a)    = atom a" |
"rexp2nae(Plus r s)  = or   (rexp2nae r) (rexp2nae s)" |
"rexp2nae(Times r s) = conc (rexp2nae r) (rexp2nae s)" |
"rexp2nae(Star r)    = star (rexp2nae r)"

declare split_paired_all[simp]

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step epsilon a = {}"
by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) \<in> steps epsilon w) = (w=[] \<and> p=q)"
by (induct "w") auto

lemma accepts_epsilon[simp]: "accepts epsilon w = (w = [])"
by (metis (mono_tags, lifting) NAe.accepts_def epsilon_def fin_def prod.sel
      start_def steps_epsilon)

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a) q) = (q = [False])"
by(simp add:atom_def)

lemma start_atom: "start (atom a) = [True]"
by(simp add:atom_def)

(* Use {x. False} = {}? *)

lemma eps_atom[simp]:
 "eps(atom a) = {}"
by (simp add:atom_def step_def)

lemma in_step_atom_Some[simp]:
 "(p,q) : step (atom a) (Some b) = (p=[True] \<and> q=[False] \<and> b=a)"
by (simp add:atom_def step_def)

lemma False_False_in_steps_atom:
  "([False],[False]) \<in> steps (atom a) w = (w = [])"
  by (induct "w") (auto simp add: relcomp_unfold)

lemma start_fin_in_steps_atom:
  "(start (atom a), [False]) \<in> steps (atom a) w = (w = [a])"
proof (induct "w")
  case Nil
  then show ?case  
    by (simp add: start_atom rtrancl_empty)
next
  case (Cons a w)
  then show ?case 
    by (simp add: False_False_in_steps_atom relcomp_unfold start_atom)
qed

lemma accepts_atom: "accepts (atom a) w = (w = [a])"
by (simp add: accepts_def start_fin_in_steps_atom fin_atom)


(******************************************************)
(*                      or                            *)
(******************************************************)

(***** lift True/False over fin *****)

lemma fin_or_True[iff]:
 "\<And>L R. fin (or L R) (True#p) = fin L p"
by(simp add:or_def)

lemma fin_or_False[iff]:
 "\<And>L R. fin (or L R) (False#p) = fin R p"
by(simp add:or_def)

(***** lift True/False over step *****)

lemma True_in_step_or[iff]:
  "\<And>L R. (True#p,q) : step (or L R) a = (\<exists>r. q = True#r \<and> (p,r) : step L a)"
by (auto simp add:or_def step_def)

lemma False_in_step_or[iff]:
  "\<And>L R. (False#p,q) : step (or L R) a = (\<exists>r. q = False#r \<and> (p,r) : step R a)"
by (auto simp add:or_def step_def)


(***** lift True/False over epsclosure *****)

lemma lemma1a:
 "(tp,tq) \<in> (eps(or L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = True#p \<Longrightarrow> \<exists>q. (p,q) \<in> (eps L)\<^sup>* \<and> tq = True#q)"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma lemma1b:
 "(tp,tq) \<in> (eps(or L R))\<^sup>* \<Longrightarrow> 
 (\<And>p. tp = False#p \<Longrightarrow> \<exists>q. (p,q) \<in> (eps R)\<^sup>* \<and> tq = False#q)"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma lemma2a:
 "(p,q) \<in> (eps L)\<^sup>*  \<Longrightarrow> (True#p, True#q) \<in> (eps(or L R))\<^sup>*"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma lemma2b:
 "(p,q) \<in> (eps R)\<^sup>*  \<Longrightarrow> (False#p, False#q) \<in> (eps(or L R))\<^sup>*"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma True_epsclosure_or[iff]:
 "(True#p,q) \<in> (eps(or L R))\<^sup>* = (\<exists>r. q = True#r \<and> (p,r) \<in> (eps L)\<^sup>*)"
by (blast dest: lemma1a lemma2a)

lemma False_epsclosure_or[iff]:
 "(False#p,q) \<in> (eps(or L R))\<^sup>* = (\<exists>r. q = False#r \<and> (p,r) \<in> (eps R)\<^sup>*)"
by (blast dest: lemma1b lemma2b)

(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
  "\<And>p. (True#p,q):steps (or L R) w = (\<exists>r. q = True # r \<and> (p,r):steps L w)"
by (induct "w"; force)

lemma lift_False_over_steps_or[iff]:
  "\<And>p. (False#p,q):steps (or L R) w = (\<exists>r. q = False#r \<and> (p,r):steps R w)"
by (induct "w"; force)

(***** Epsilon closure of start state *****)

lemma unfold_rtrancl2:
  "R\<^sup>* = Id \<union> (R O R\<^sup>*)"
by (metis r_comp_rtrancl_eq rtrancl_unfold)

lemma in_unfold_rtrancl2:
 "(p,q) \<in> R\<^sup>* = (q = p \<or> (\<exists>r. (p,r) \<in> R \<and> (r,q) \<in> R\<^sup>*))"
  by (metis converse_rtranclE converse_rtrancl_into_rtrancl rtrancl.simps)

lemmas [iff] = in_unfold_rtrancl2[where ?p = "start(or L R)"] for L R

lemma start_eps_or[iff]:
 "\<And>L R. (start(or L R),q) \<in> eps(or L R) = 
       (q = True#start L \<or> q = False#start R)"
by (simp add:or_def step_def)

lemma not_start_step_or_Some[iff]:
 "\<And>L R. (start(or L R),q) \<notin> step (or L R) (Some a)"
by (simp add:or_def step_def)

lemma steps_or:
 "((start (RegExp2NAe.or L R), q)
     \<in> NAe.steps (RegExp2NAe.or L R) w) \<longleftrightarrow>
    (w = [] \<and> q = start (RegExp2NAe.or L R) \<or>
     (\<exists>p. q = True # p \<and> (start L, p) \<in> NAe.steps L w \<or>
          q = False # p \<and> (start R, p) \<in> NAe.steps R w))"
  by (cases "w"; simp; blast) 

lemma start_or_not_final[iff]:
 "\<And>L R. \<not> fin (or L R) (start(or L R))"
by (simp add:or_def)

lemma accepts_or:
  "accepts (or L R) w = (accepts L w | accepts R w)"
by (auto simp add:accepts_def steps_or)


(******************************************************)
(*                      conc                          *)
(******************************************************)

(** True/False in fin **)

lemma in_conc_True[iff]:
 "\<And>L R. fin (conc L R) (True#p) = False"
by (simp add:conc_def)

lemma fin_conc_False[iff]:
 "\<And>L R. fin (conc L R) (False#p) = fin R p"
by (simp add:conc_def)

(** True/False in step **)

lemma True_step_conc[iff]:
 "\<And>L R. (True#p,q) : step (conc L R) a = 
       ((\<exists>r. q=True#r \<and> (p,r): step L a) | 
        (fin L p \<and> a=None \<and> q=False#start R))"
by (simp add:conc_def step_def) (blast)

lemma False_step_conc[iff]:
 "\<And>L R. (False#p,q) : step (conc L R) a = 
       (\<exists>r. q = False#r \<and> (p,r) : step R a)"
by (simp add:conc_def step_def) (blast)

(** False in epsclosure **)

lemma lemma1b':
 "(tp,tq) \<in> (eps(conc L R))\<^sup>* \<Longrightarrow> 
  (\<And>p. tp = False#p \<Longrightarrow> \<exists>q. (p,q) \<in> (eps R)\<^sup>* \<and> tq = False#q)"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma lemma2b':
  "(p,q) \<in> (eps R)\<^sup>* \<Longrightarrow> (False#p, False#q) \<in> (eps(conc L R))\<^sup>*"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma False_epsclosure_conc[iff]:
  "((False # p, q) \<in> (eps (conc L R))\<^sup>*) = (\<exists>r. q = False # r \<and> (p, r) \<in> (eps R)\<^sup>*)"
by (meson lemma1b' lemma2b')

(** False in steps **)

lemma False_steps_conc[iff]:
  "\<And>p. (False#p,q)\<in> steps (conc L R) w = (\<exists>r. q=False#r \<and> (p,r)\<in> steps R w)"
by (induct "w"; force)

(** True in epsclosure **)

lemma True_True_eps_concI:
 "(p,q) \<in> (eps L)\<^sup>* \<Longrightarrow> (True#p,True#q) \<in> (eps(conc L R))\<^sup>*"
by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)

lemma True_True_steps_concI:
  "\<And>p. (p,q) \<in> steps L w \<Longrightarrow> (True#p,True#q) \<in> steps (conc L R) w"
proof (induct "w")
  case Nil
  then show ?case 
    by (simp add: True_True_eps_concI)
next
  case (Cons a w)
  then show ?case
    by (auto intro: True_True_eps_concI)
qed

lemma lem:
 "\<And>L R. (p,q) : step R None \<Longrightarrow> (False#p, False#q) : step (conc L R) None"
by(simp add: conc_def step_def)

lemma lemma2b'':
 "(p,q) \<in> (eps R)\<^sup>* \<Longrightarrow> (False#p, False#q) \<in> (eps(conc L R))\<^sup>*"
  by blast

lemma True_False_eps_concI:
 "\<And>L R. fin L p \<Longrightarrow> (True#p, False#start R) \<in> eps(conc L R)"
by(simp add: conc_def step_def)

lemma True_epsclosure_conc[iff]:
 "((True#p,q) \<in> (eps(conc L R))\<^sup>*) = 
 ((\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> q = True#r) \<or>
  (\<exists>r. (p,r) \<in> (eps L)\<^sup>* \<and> fin L r \<and>
        (\<exists>s. (start R, s) \<in> (eps R)\<^sup>* \<and> q = False#s)))"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (induct rule:rtrancl_induct; blast intro: rtrancl_into_rtrancl)
  assume ?rhs
  then show ?lhs
  proof (elim disjE exE conjE)
    fix r
    assume "(p, r) \<in> (eps L)\<^sup>*" "q = True # r"
    then show "(True # p, q) \<in> (eps (RegExp2NAe.conc L R))\<^sup>*"
      by (simp add: True_True_eps_concI)
  next
    fix r s
    assume "(p, r) \<in> (eps L)\<^sup>*" "fin L r" "(start R, s) \<in> (eps R)\<^sup>*" "q = False # s"
    then have "(True # r, False # s) \<in> (eps (RegExp2NAe.conc L R))\<^sup>*"
      by (meson False_epsclosure_conc True_step_conc in_unfold_rtrancl2)
    then show "(True # p, q) \<in> (eps (RegExp2NAe.conc L R))\<^sup>*"
      by (metis True_True_eps_concI \<open>(p, r) \<in> (eps L)\<^sup>*\<close> \<open>q = False # s\<close> rtrancl_trans)
  qed
qed

(** True in steps **)

lemma True_steps_concD:
 "(True#p,q) \<in> steps (conc L R) w \<Longrightarrow>
     ((\<exists>r. (p,r) \<in> steps L w \<and> q = True#r)  \<or>
      (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and>
              (\<exists>s. (start R,s) \<in> steps R v \<and> q = False#s))))"
proof (induction w arbitrary: p)
  case Nil
  then show ?case by auto
next
  case (Cons a w)
  obtain u v r
    where \<section>: "(u,v) \<in> step (RegExp2NAe.conc L R) (Some a)"
      "(v, q) \<in> NAe.steps (RegExp2NAe.conc L R) w"
      "(p, r) \<in> (eps L)\<^sup>*"
      and "u = True # r \<or> fin L r \<and> (\<exists>s. (start R, s) \<in> (eps R)\<^sup>* \<and> u = False # s)"
    using Cons.prems
    by simp blast
  then consider "u = True # r" | s where "fin L r" "(start R, s) \<in> (eps R)\<^sup>* \<and> u = False # s"
    by blast
  then show ?case
  proof cases
    case 1
    with \<section> obtain r' where r': "(True#r',q) \<in> steps (conc L R) w"
           and \<dagger>: "(r, r') \<in> step L (Some a)" "v = True # r'"
      by blast
    from Cons.IH [OF r'] show ?thesis
    proof (elim exE disjE conjE)
      fix u' v' r'' s'
      assume \<ddagger>: "w = u' @ v'" "(start R, s') \<in> NAe.steps R v'" "q = False # s'"
        and "fin L r''" "(r', r'') \<in> NAe.steps L u'"
      then have "\<exists>r. (p, r) \<in> (eps L)\<^sup>* O step L (Some a) O NAe.steps L u' \<and> fin L r"
        using \<dagger> \<section> by blast 
      with \<ddagger> show ?thesis
        by (metis NAe.steps.simps(2) append_Cons) 
    qed (use 1 \<section> Cons in auto)
  next
    case 2
    with \<section> show ?thesis
      by fastforce
  qed
qed

lemma True_steps_conc:
 "(True#p,q) \<in> steps (conc L R) w = 
 ((\<exists>r. (p,r) \<in> steps L w \<and> q = True#r)  | 
  (\<exists>u v. w = u@v \<and> (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and> 
          (\<exists>s. (start R,s) \<in> steps R v \<and> q = False#s))))"
by (blast dest: True_steps_concD
    intro: True_True_steps_concI in_steps_epsclosure)

(** starting from the start **)

lemma start_conc:
  "\<And>L R. start(conc L R) = True#start L"
by (simp add: conc_def)

lemma final_conc:
 "\<And>L R. fin(conc L R) p = (\<exists>s. p = False#s \<and> fin R s)"
by (simp add:conc_def split: list.split)

lemma accepts_conc:
 "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
by (fastforce simp add: accepts_def True_steps_conc final_conc start_conc)

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma True_in_eps_star[iff]:
 "\<And>A. (True#p,q) \<in> eps(star A) = 
     ( (\<exists>r. q = True#r \<and> (p,r) \<in> eps A) \<or> (fin A p \<and> q = True#start A) )"
by (simp add:star_def step_def) (blast)

lemma True_True_step_starI:
  "\<And>A. (p,q) : step A a \<Longrightarrow> (True#p, True#q) : step (star A) a"
by (simp add:star_def step_def)

lemma True_True_eps_starI:
  "(p,r) \<in> (eps A)\<^sup>* \<Longrightarrow> (True#p, True#r) \<in> (eps(star A))\<^sup>*"
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  then show ?case by (blast intro: True_True_step_starI rtrancl_into_rtrancl)
qed

lemma True_start_eps_starI:
 "\<And>A. fin A p \<Longrightarrow> (True#p,True#start A) \<in> eps(star A)"
by (simp add:star_def step_def)

lemma True_eps_star[iff]:
 "((True#p,s) \<in> (eps(star A))\<^sup>*) = 
 (\<exists>r. ((p,r) \<in> (eps A)\<^sup>* \<or>
        (\<exists>q. (p,q) \<in> (eps A)\<^sup>* \<and> fin A q \<and> (start A,r) \<in> (eps A)\<^sup>*)) \<and>
       s = True#r)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case
      by blast
  next
    case (step y z)
    then show ?case
      by (meson True_in_eps_star rtrancl.rtrancl_into_rtrancl rtrancl.rtrancl_refl)
  qed
  show "?rhs \<Longrightarrow> ?lhs"
  by (metis (no_types, opaque_lifting) rtrancl_trans  True_start_eps_starI True_True_eps_starI converse_rtrancl_into_rtrancl)
qed

(** True in step Some **)

lemma True_step_star[iff]:
 "\<And>A. (True#p,r) \<in> step (star A) (Some a) =
     (\<exists>q. (p,q) \<in> step A (Some a) \<and> r=True#q)"
by (simp add:star_def step_def) (blast)


(** True in steps **)

(* reverse list induction! Complicates matters for conc? *)
lemma True_start_steps_starD:
  "(True#start A,rr) \<in> steps (star A) w \<Longrightarrow>
     (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = True#r))"
proof (induction w arbitrary: rr rule: rev_induct)
  case Nil
  then show ?case
    using split_list_cycles by fastforce
next
  case (snoc x xs)
  then obtain u v 
    where \<section>: "(v, rr) \<in> (eps (RegExp2NAe.star A))\<^sup>*"
        "(True # start A, u) \<in> NAe.steps (RegExp2NAe.star A) xs"
        "(u, v) \<in> step (RegExp2NAe.star A) (Some x)"
    by (auto simp: O_assoc[symmetric] epsclosure_steps)
  then obtain uss vs r 
    where  "xs = concat uss @ vs" "(\<forall>a\<in>set uss. NAe.accepts A a)" 
           "(start A, r) \<in> NAe.steps A vs"  "u = True # r"
    using snoc.IH by meson
  with \<section> show ?case
    apply (clarify; elim disjE exE)
     apply (rule_tac x = "uss" in exI)
     apply (rule_tac x = "vs@[x]" in exI)
     apply (fastforce simp add: O_assoc[symmetric] epsclosure_steps)
    apply (rule_tac x = "uss@[vs@[x]]" in exI)
    apply (rule_tac x = "[]" in exI)
    apply (fastforce simp add: accepts_def)
    done
qed

lemma True_True_steps_starI:
  "\<And>p. (p,q) \<in> steps A w \<Longrightarrow> (True#p,True#q) \<in> steps (star A) w"
by (induct "w") (auto intro: True_True_eps_starI True_True_step_starI)

lemma steps_star_cycle:
 "(\<forall>u \<in> set us. accepts A u) \<Longrightarrow>
 (True#start A,True#start A) \<in> steps (star A) (concat us)"
proof (induct "us")
  case Nil
  then show ?case
    by simp
next
  case (Cons a us)
  then have "(True # start A, True # start A) \<in> NAe.steps (RegExp2NAe.star A) (concat us)"
    by auto
  moreover
  obtain q where "(start A, q) \<in> NAe.steps A a" "fin A q"
    by (meson Cons.prems NAe.accepts_def list.set_intros(1))
  ultimately 
    have "(True # start A, True # start A)
              \<in> NAe.steps (RegExp2NAe.star A) a O NAe.steps (RegExp2NAe.star A) (concat us)"
    by (meson True_True_steps_starI True_start_eps_starI in_epsclosure_steps r_into_rtrancl
        relcomp.relcompI)
  then show ?case
    by (auto simp: accepts_def)
qed

(* Better stated directly with start(star A)? Loop in star A back to start(star A)?*)
lemma True_start_steps_star:
 "(True#start A,rr) \<in> steps (star A) w = 
 (\<exists>us v. w = concat us @ v \<and>
             (\<forall>u\<in>set us. accepts A u) \<and>
             (\<exists>r. (start A,r) \<in> steps A v \<and> rr = True#r))"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: True_start_steps_starD)
  show "?rhs \<Longrightarrow> ?lhs"
    by (blast intro: steps_star_cycle True_True_steps_starI)
qed

(** the start state **)

lemma start_step_star[iff]:
  "\<And>A. (start(star A),r) : step (star A) a = (a=None \<and> r = True#start A)"
by (simp add:star_def step_def)

lemmas epsclosure_start_step_star =
  in_unfold_rtrancl2[where ?p = "start (star A)"] for A

lemma start_steps_star:
  "(start(star A),r) \<in> steps (star A) w \<longleftrightarrow>
   ((w=[] \<and> r = start(star A)) | (True#start A,r) \<in> steps (star A) w)"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (cases w)
    case Nil
    with L show ?thesis 
      by (simp add: epsclosure_start_step_star)
  next
    case (Cons u us)
    with L show ?thesis
      by (clarsimp simp add: epsclosure_start_step_star) blast
  qed
next 
  have ?lhs if "(True # start A, r) \<in> NAe.steps (RegExp2NAe.star A) w"
    by (meson in_steps_epsclosure r_into_rtrancl start_step_star that)
  then show "?rhs \<Longrightarrow> ?lhs" by auto
qed

lemma fin_star_True[iff]: "\<And>A. fin (star A) (True#p) = fin A p"
by (simp add:star_def)

lemma fin_star_start[iff]: "\<And>A. fin (star A) (start(star A))"
by (simp add:star_def)

(* too complex! Simpler if loop back to start(star A)? *)
lemma accepts_star:
 "accepts (star A) w \<longleftrightarrow> (\<exists>us. (\<forall>u \<in> set(us). accepts A u) \<and> (w = concat us))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain q where "(start (RegExp2NAe.star A), q) \<in> NAe.steps (RegExp2NAe.star A) w"
                 and qfin: "fin (RegExp2NAe.star A) q"
    by (auto simp: accepts_def)
  then consider "w = []" "q = start (RegExp2NAe.star A)" | "(True # start A, q) \<in> NAe.steps (RegExp2NAe.star A) w"
    by (auto simp add: start_steps_star)
  then show ?rhs
  proof cases
    case 1
    then show ?thesis
      using split_list_first by fastforce
  next
    case 2
    with qfin obtain us v r where \<section>: "w = concat us @ v" 
           "\<forall>u\<in>set us. NAe.accepts A u" "(start A, r) \<in> NAe.steps A v" "fin A r"
      using True_start_steps_starD qfin by blast
    have "concat us @ v = concat (us @ [v])"
      by auto
    with 2 \<section>
     show ?thesis
       by (metis NAe.accepts_def rotate1.simps(2) set_ConsD set_rotate1)
  qed
next
  assume ?rhs
  then obtain us where us: "\<forall>u\<in>set us. \<exists>q. (start A, q) \<in> NAe.steps A u \<and> fin A q"
           "w = concat us"
    using NAe.accepts_def by blast
  show ?lhs
  proof (cases us rule: rev_exhaust)
    case Nil
    with us show ?thesis
      by (force simp: NAe.accepts_def)
  next
    case (snoc ys y)
    with us show ?thesis
      apply simp
      by (metis NAe.accepts_def NAe.steps_append True_start_steps_star fin_star_True
          start_steps_star)
  qed
qed


(***** Correctness of r2n *****)

lemma accepts_rexp2nae:
 "\<And>w. accepts (rexp2nae r) w = (w : lang r)"
proof (induct "r")
  case Zero
  then show ?case
    by (simp add: accepts_def)
next
  case (Times r1 r2)
  then show ?case
    by (metis accepts_conc concE concI lang.simps(5) rexp2nae.simps(5))
next
  case (Star r)
  then show ?case
    by (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
qed (auto simp add: accepts_atom accepts_or)

end
