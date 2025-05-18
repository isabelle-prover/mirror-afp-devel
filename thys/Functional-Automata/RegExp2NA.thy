(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "From regular expressions directly to nondeterministic automata"

theory RegExp2NA
imports "Regular-Sets.Regular_Exp" NA 
begin

type_synonym 'a bitsNA = "('a,bool list)na"

definition
"atom"  :: "'a \<Rightarrow> 'a bitsNA" where
"atom a = ([True],
            \<lambda>b s. if s=[True] \<and> b=a then {[False]} else {},
            \<lambda>s. s=[False])"

definition
 or :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"or = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   ([],
    \<lambda>a s. case s of
            [] \<Rightarrow> (True ## dl a ql) \<union> (False ## dr a qr)
          | left#s \<Rightarrow> if left then True ## dl a s
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> (fl ql | fr qr)
                | left#s \<Rightarrow> if left then fl s else fr s))"

definition
 conc :: "'a bitsNA \<Rightarrow> 'a bitsNA \<Rightarrow> 'a bitsNA" where
"conc = (\<lambda>(ql,dl,fl)(qr,dr,fr).
   (True#ql,
    \<lambda>a s. case s of
            [] \<Rightarrow> {}
          | left#s \<Rightarrow> if left then (True ## dl a s) \<union>
                                   (if fl s then False ## dr a qr else {})
                              else False ## dr a s,
    \<lambda>s. case s of [] \<Rightarrow> False | left#s \<Rightarrow> left \<and> fl s \<and> fr qr | \<not>left \<and> fr s))"

definition
 epsilon :: "'a bitsNA" where
"epsilon = ([],\<lambda>a s. {}, \<lambda>s. s=[])"

definition
 plus :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
"plus = (\<lambda>(q,d,f). (q, \<lambda>a s. d a s \<union> (if f s then d a q else {}), f))"

definition
 star :: "'a bitsNA \<Rightarrow> 'a bitsNA" where
"star A = or epsilon (plus A)"

primrec rexp2na :: "'a rexp \<Rightarrow> 'a bitsNA" where
"rexp2na Zero       = ([], \<lambda>a s. {}, \<lambda>s. False)" |
"rexp2na One        = epsilon" |
"rexp2na(Atom a)    = atom a" |
"rexp2na(Plus r s)  = or (rexp2na r) (rexp2na s)" |
"rexp2na(Times r s) = conc (rexp2na r) (rexp2na s)" |
"rexp2na(Star r)    = star (rexp2na r)"

declare split_paired_all[simp]

(******************************************************)
(*                       atom                         *)
(******************************************************)

lemma fin_atom: "(fin (atom a) q) = (q = [False])"
  by(simp add:atom_def)

lemma start_atom: "start (atom a) = [True]"
  by(simp add:atom_def)

lemma in_step_atom_Some[simp]:
  "(p,q) : step (atom a) b = (p=[True] \<and> q=[False] \<and> b=a)"
  by (simp add: atom_def step_def)

lemma False_False_in_steps_atom:
  "([False],[False]) \<in> steps (atom a) w = (w = [])"
  by (induct "w") (auto simp add: relcomp_unfold)

lemma start_fin_in_steps_atom:
  "(start (atom a), [False]) \<in> steps (atom a) w = (w = [a])"
  by (induct "w") (auto simp: False_False_in_steps_atom relcomp_unfold start_atom)

lemma accepts_atom:
  "accepts (atom a) w = (w = [a])"
  by (simp add: accepts_conv_steps start_fin_in_steps_atom fin_atom)

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
  "\<And>L R. (True#p,q) : step (or L R) a = (\<exists>r. q = True#r \<and> (p,r) \<in> step L a)"
  by (force simp add:or_def step_def)

lemma False_in_step_or[iff]:
  "\<And>L R. (False#p,q) : step (or L R) a = (\<exists>r. q = False#r \<and> (p,r) \<in> step R a)"
  by (force simp add:or_def step_def)


(***** lift True/False over steps *****)

lemma lift_True_over_steps_or[iff]:
  "\<And>p. (True#p,q)\<in>steps (or L R) w = (\<exists>r. q = True # r \<and> (p,r) \<in> steps L w)"
  by (induct "w") force+

lemma lift_False_over_steps_or[iff]:
  "\<And>p. (False#p,q)\<in>steps (or L R) w = (\<exists>r. q = False#r \<and> (p,r)\<in>steps R w)"
  by (induct "w") force+

(** From the start  **)

lemma start_step_or[iff]:
  "\<And>L R. (start(or L R),q) : step(or L R) a = 
         (\<exists>p. (q = True#p \<and> (start L,p) : step L a) | 
               (q = False#p \<and> (start R,p) : step R a))"
  by (force simp add:or_def step_def)

lemma steps_or:
  "(start(or L R), q) \<in> steps (or L R) w = 
  ( (w = [] \<and> q = start(or L R)) | 
    (w \<noteq> [] \<and> (\<exists>p.  q = True  # p \<and> (start L,p) \<in> steps L w | 
                      q = False # p \<and> (start R,p) \<in> steps R w)))"
  by (cases w; fastforce)

lemma fin_start_or[iff]:
  "\<And>L R. fin (or L R) (start(or L R)) = (fin L (start L) | fin R (start R))"
  by (simp add:or_def)

lemma accepts_or[iff]:
  "accepts (or L R) w = (accepts L w | accepts R w)"
  by (cases w; fastforce simp add: accepts_conv_steps steps_or)

(******************************************************)
(*                      conc                        *)
(******************************************************)

(** True/False in fin **)

lemma fin_conc_True[iff]:
  "\<And>L R. fin (conc L R) (True#p) = (fin L p \<and> fin R (start R))"
  by(simp add:conc_def)

lemma fin_conc_False[iff]:
  "\<And>L R. fin (conc L R) (False#p) = fin R p"
  by(simp add:conc_def)


(** True/False in step **)

lemma True_step_conc[iff]:
  "\<And>L R. (True#p,q) : step (conc L R) a = 
        ((\<exists>r. q=True#r \<and> (p,r): step L a) | 
         (fin L p \<and> (\<exists>r. q=False#r \<and> (start R,r) : step R a)))"
  by (force simp add:conc_def step_def)

lemma False_step_conc[iff]:
  "\<And>L R. (False#p,q) : step (conc L R) a = 
       (\<exists>r. q = False#r \<and> (p,r) : step R a)"
  by (force simp add:conc_def step_def)

(** False in steps **)

lemma False_steps_conc[iff]:
  "\<And>p. (False#p,q) \<in> steps (conc L R) w = (\<exists>r. q=False#r \<and> (p,r) \<in> steps R w)"
  by (induct "w"; force)

(** True in steps **)

lemma True_True_steps_concI:
  "\<And>L R p. (p,q) \<in> steps L w \<Longrightarrow> (True#p,True#q) \<in> steps (conc L R) w"
  by (induct "w"; force)

lemma True_False_step_conc[iff]:
  "\<And>L R. (True#p,False#q) : step (conc L R) a = 
         (fin L p \<and> (start R,q) : step R a)"
  by simp

lemma True_steps_concD:
  "(True#p,q) \<in> steps (conc L R) w \<Longrightarrow>
     ((\<exists>r. (p,r) \<in> steps L w \<and> q = True#r)  \<or> 
  (\<exists>u a v. w = u@a#v \<and> 
            (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) \<in> steps R v \<and> q = False#t)))))"
proof (induction "w" arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  show ?case
    using Cons.prems
    apply clarsimp
    apply (elim exE disjE)
     apply (auto dest!: Cons.IH)
    apply (metis Cons_eq_appendI relcomp.relcompI steps.simps(2))
    apply force
    done
qed

lemma True_steps_conc:
  "(True#p,q) \<in> steps (conc L R) w = 
 ((\<exists>r. (p,r) \<in> steps L w \<and> q = True#r)  \<or>
  (\<exists>u a v. w = u@a#v \<and>
            (\<exists>r. (p,r) \<in> steps L u \<and> fin L r \<and> 
            (\<exists>s. (start R,s) : step R a \<and> 
            (\<exists>t. (s,t) \<in> steps R v \<and> q = False#t)))))"
  by(force dest!: True_steps_concD intro!: True_True_steps_concI)

(** starting from the start **)

lemma start_conc:
  "\<And>L R. start(conc L R) = True#start L"
  by (simp add:conc_def)

lemma final_conc:
  "\<And>L R. fin(conc L R) p = ((fin R (start R) \<and> (\<exists>s. p = True#s \<and> fin L s)) \<or>
                           (\<exists>s. p = False#s \<and> fin R s))"
  by (force simp add:conc_def split: list.split)

lemma accepts_conc:
  "accepts (conc L R) w = (\<exists>u v. w = u@v \<and> accepts L u \<and> accepts R v)"
proof -
  have "\<exists>u v. w = u @ v \<and> accepts L u \<and> accepts R v"
    if "accepts (RegExp2NA.conc L R) w"
    using that unfolding accepts_conv_steps True_steps_conc start_conc
    by (elim exE disjE conjE) force+
  moreover have "accepts (RegExp2NA.conc L R) (u @ v)"
    if "w = u @ v" and "accepts L u" and "accepts R v" for u v
    using that unfolding accepts_conv_steps True_steps_conc final_conc start_conc
    by (cases v; fastforce)
  ultimately show ?thesis
    by auto
qed

(******************************************************)
(*                     epsilon                        *)
(******************************************************)

lemma step_epsilon[simp]: "step epsilon a = {}"
  by(simp add:epsilon_def step_def)

lemma steps_epsilon: "((p,q) \<in> steps epsilon w) = (w=[] \<and> p=q)"
  by (induct "w") auto

lemma accepts_epsilon[iff]: "accepts epsilon w = (w = [])"
  unfolding steps_epsilon accepts_conv_steps
  by (auto simp add: epsilon_def)

(******************************************************)
(*                       plus                         *)
(******************************************************)

lemma start_plus[simp]: "\<And>A. start (plus A) = start A"
  by(simp add:plus_def)

lemma fin_plus[iff]: "\<And>A. fin (plus A) = fin A"
  by(simp add:plus_def)

lemma step_plusI:
  "\<And>A. (p,q) : step A a \<Longrightarrow> (p,q) : step (plus A) a"
  by(simp add:plus_def step_def)

lemma steps_plusI: "\<And>p. (p,q) \<in> steps A w \<Longrightarrow> (p,q) \<in> steps (plus A) w"
  by (induct w; force intro: step_plusI)

lemma step_plus_conv[iff]:
  "\<And>A. ((p, r) \<in> step (RegExp2NA.plus A) a) \<longleftrightarrow> ((p, r) \<in> step A a \<or> fin A p \<and> (start A, r) \<in> step A a)"
  by(simp add:plus_def step_def)

lemma fin_steps_plusI:
  "\<lbrakk>(start A, q) \<in> steps A u; u \<noteq> []; fin A p\<rbrakk> \<Longrightarrow> (p, q) \<in> steps (RegExp2NA.plus A) u"
  by (cases "u"; force intro: steps_plusI)

(* reverse list induction! Complicates matters for conc? *)
lemma start_steps_plusD[rule_format]:
  "(start A,r) \<in> steps (plus A) w \<Longrightarrow>
     (\<exists>us v. w = concat us @ v \<and> (\<forall>u\<in>set us. accepts A u) \<and> (start A,r) \<in> steps A v)"
proof (induction w arbitrary: r rule: rev_induct)
  case Nil
  then show ?case
    by (intro exI [where x="[]"]) auto
next
  case (snoc x xs)
  then obtain us v z 
    where D: "(z, r) \<in> step A x \<or> fin A z \<and> (start A, r) \<in> step A x"
      and E: "(start A, z) \<in> steps A v" 
      and F: "\<forall>x\<in>set us. accepts A x" "xs = concat us @ v"
    by force
  show ?case
    using D
  proof
    assume "(z, r) \<in> step A x"
    with E have "(start A, r) \<in> steps A v O step A x"
      by blast
    with F show ?thesis
      by fastforce
  next
    assume "fin A z \<and> (start A, r) \<in> step A x"
    with E F show ?thesis
      by (force simp add: accepts_conv_steps intro: exI [where x = "us@[v]"])
  qed 
qed

lemma steps_star_cycle [rule_format]:
  "us \<noteq> [] \<Longrightarrow> (\<forall>u \<in> set us. accepts A u) \<longrightarrow> accepts (plus A) (concat us)"
proof (induction us rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc u us)
  show ?case
  proof (cases "us = []")
    case True
    then show ?thesis
      by (auto simp: accepts_conv_steps intro: steps_plusI)
  next
    case False
    then show ?thesis
    proof (clarsimp simp: accepts_conv_steps False snoc)
      fix q 
      assume \<section>: "\<forall>x\<in>set us. \<exists>q. (start A, q) \<in> steps A x \<and> fin A q"
                "(start A, q) \<in> steps A u" "fin A q"
      with snoc.IH show "\<exists>q. (start A, q) \<in> steps (RegExp2NA.plus A) (concat us) O steps (RegExp2NA.plus A) u \<and> fin A q"
      proof (cases "u = []")
        case False
        with \<section> snoc.IH \<open>us \<noteq> []\<close> show ?thesis 
          by (auto simp: accepts_conv_steps intro: fin_steps_plusI)
      qed (simp add: False accepts_conv_steps)
    qed
  qed
qed

lemma accepts_plus [iff]:
  "accepts (plus A) w = (\<exists>us. us \<noteq> [] \<and> w = concat us \<and> (\<forall>u \<in> set us. accepts A u))"
proof -
  { assume "accepts (RegExp2NA.plus A) w"
    then obtain q us v where "fin A q" "w = concat us @ v" 
                   "\<forall>u\<in>set us. accepts A u" "(start A, q) \<in> steps A v"
      by (auto simp: accepts_conv_steps dest: start_steps_plusD)
    then have "\<exists>us. us \<noteq> [] \<and> w = concat us \<and> (\<forall>u\<in>set us. accepts A u)"
      by (intro exI [where x = "us@[v]"]) (auto simp: accepts_conv_steps)
  }
  then show ?thesis
    by (auto simp: intro: steps_star_cycle)
qed

(******************************************************)
(*                       star                         *)
(******************************************************)

lemma accepts_star:
  "accepts (star A) w = (\<exists>us. (\<forall>u \<in> set us. accepts A u) \<and> w = concat us)" (is "_ = ?rhs")
  unfolding star_def
  by (metis accepts_epsilon accepts_or accepts_plus concat.simps(1) empty_iff list.set(1))

(***** Correctness of r2n *****)

lemma accepts_rexp2na:
  "\<And>w. accepts (rexp2na r) w = (w \<in> lang r)"
proof (induction r)
  case Zero
  then show ?case
    by (simp add: accepts_conv_steps)
next
  case (Times r1 r2)
  then show ?case by (force simp add: accepts_conc Regular_Set.conc_def)
next
  case (Star r)
  then show ?case by (simp add: accepts_star in_star_iff_concat subset_iff Ball_def)
qed (auto simp: accepts_atom)

end
