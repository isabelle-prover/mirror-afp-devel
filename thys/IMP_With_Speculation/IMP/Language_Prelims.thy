section \<open>Prelim\<close>

text \<open> This theory contains some preliminary facts about reflective transistive closure and the comparisons of two symmetric distances, where the later is useful for Relative Security invariants\<close>

theory Language_Prelims imports Main
begin


lemma length_1_butlast[simp]: "length xs = Suc 0 \<Longrightarrow> butlast xs = []"
by (cases xs, auto)

(* The distance between two sets *)

definition "dist A B \<equiv> (A - B) \<union> (B - A)"

definition "distL A B \<equiv> (A - B)"

definition "distR A B \<equiv> (B - A)"

lemma distLR_int_empt[simp]:"distL A B \<inter> distR A B = {} " 
  unfolding distR_def distL_def 
  by auto

lemma distLR_imp_dist:"distL A B \<subseteq> distL C D \<and> distR A B \<subseteq> distR C D \<Longrightarrow> dist A B \<subseteq> dist C D"
  unfolding dist_def distL_def distR_def 
  by auto


lemma dist_insert: "dist A B = dist C D \<Longrightarrow> dist (insert x A) (insert x B) = dist (insert x C) (insert x D)"
  unfolding dist_def by auto

lemma dist_refl[simp,intro]: "dist A A = {}"
unfolding dist_def by auto

lemma dist_empty_iff[simp]: "dist A B = {} \<longleftrightarrow> A = B"
unfolding dist_def by auto


lemma dist_match_grow[simp,intro]:"
        dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
     x \<in> dist (insert a ls3) (insert a ls4) \<Longrightarrow> 
     x \<in> dist (insert a ls1) (insert a ls2)"
  unfolding dist_def by auto

lemma dist_ignore[simp,intro]:"
     dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
     x \<in> dist (insert a ls3) (insert a ls4) \<Longrightarrow>
     x \<in> dist ls1 ls2"

  unfolding dist_def by auto

(*cases: if x is not in either or in both, then dist (insert x A) (insert x B) = dist A B
  otherwise x is in one but not the other, then dist (insert x A) (insert x B) = dist A B - {x}
                                           hence
                                                dist (insert x A) (insert x B) \<subseteq> dist A B

  thus 
          dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
          dist (insert a ls3) (insert a ls4) \<subseteq> dist ls1 ls2
*)

lemma dist_insert_su[simp,intro]: "dist (insert x A) (insert x B) \<subseteq> dist A B"
  unfolding dist_def by auto

lemma dist_ignore_insert[simp,intro]:"
     dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
     dist (insert a ls3) (insert a ls4) \<subseteq> dist ls1 ls2"

  unfolding dist_def by auto

(*
lemma desired:"
        dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
        dist (insert a ls3) (insert b ls4) \<subseteq> dist (insert a ls1) (insert b ls2)"
  ls3 = {}
  ls4 = {}
  ls1 = {a\<^sub>1}
  ls2 = {}
  a = a\<^sub>2
  b = a\<^sub>1
*)

(*a sufficiently powerful premise*)
lemma dist_match_diff[simp,intro]:"
        dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
        ls1 \<subset> ls3 \<Longrightarrow> ls2 \<subset> ls4 \<Longrightarrow>
        dist (insert a ls3) (insert b ls4) \<subseteq> dist (insert a ls1) (insert b ls2)"
  unfolding dist_def by auto

lemma list_one[intro]:"A \<noteq> {a} \<Longrightarrow> A \<subseteq> {a} \<Longrightarrow> A = {}"
  by auto

lemma dist_match_grow_diff[simp,intro]:"
        dist ls3 ls4 \<subseteq> dist ls1 ls2 \<Longrightarrow>
        ls1 \<subseteq> ls3 \<Longrightarrow> ls2 \<subseteq> ls4 \<Longrightarrow>
     x \<in> dist (insert a ls3) (insert b ls4) \<Longrightarrow> 
     x \<in> dist (insert a ls1) (insert b ls2)"
  unfolding dist_def by auto

lemma dist_match_grow_diff1[simp,intro]:"dist C D \<subseteq> dist A B \<Longrightarrow>
    A \<subseteq> C \<Longrightarrow>
    B \<subseteq> D \<Longrightarrow>
    dist (insert a C) (insert b D)
    \<subseteq> dist (insert a A) (insert b B)" 
  using dist_match_grow_diff subsetI by auto

lemma dist_eq_grow_ab:"dist C D \<subseteq> dist A B \<Longrightarrow>
    A \<subseteq> C \<Longrightarrow>
    B \<subseteq> D \<Longrightarrow>
    dist (C \<union> a) (D \<union> b)
    \<subseteq> dist (A \<union> a) (B \<union> b)" 
  unfolding dist_def by auto 

lemma dist_eq_grow:"
dist C D \<subseteq> dist A B \<Longrightarrow> A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow>
dist (C \<union> a) (D \<union> a) \<subseteq> dist (A \<union> a) (B \<union> a)"
  using dist_eq_grow_ab by metis

lemma dist_ignore_grow:"
dist C D \<subseteq> dist A B \<Longrightarrow> A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow>
dist (C \<union> a) (D \<union> a) \<subseteq> dist A B"
  unfolding dist_def by auto


(*distL intros*)

lemma distL_insert: "distL A B = distL C D \<Longrightarrow> distL (insert x A) (insert x B) = distL (insert x C) (insert x D)"
  unfolding distL_def by auto

lemma distL_refl[simp,intro]: "distL A A = {}"
unfolding distL_def by auto

lemma distL_insert_su[simp,intro]: "distL (insert x A) (insert x B) \<subseteq> distL A B"
  unfolding distL_def by auto


(*distR intros*)
lemma distR_insert: "distR A B = distR C D \<Longrightarrow> distR (insert x A) (insert x B) = distR (insert x C) (insert x D)"
  unfolding distR_def by auto

lemma distR_refl[simp,intro]: "distR A A = {}"
unfolding distR_def by auto

lemma distR_insert_su[simp,intro]: "distR (insert x A) (insert x B) \<subseteq> distR A B"
unfolding distR_def by auto




lemma insert_null_grow[simp]:"a \<in> ls3 \<Longrightarrow> insert a ls3 = ls3" by auto

lemma distL_match_grow_aux:"distL ls3 ls4 \<subseteq> distL ls1 ls2 \<Longrightarrow>
ls1 \<subset> ls3 \<Longrightarrow>ls2 \<subset> ls4 \<Longrightarrow>
        distL (insert a ls3) (insert b ls4)
     \<subseteq> distL (insert a ls1) (insert b ls2)"
  unfolding distL_def
  apply (cases "a=b")
  subgoal by blast
  subgoal
    apply (cases "a \<in> ls3", cases "b \<in> ls4")  
    apply simp
      apply (cases "b \<in> ls2")
    by (cases "b \<in> ls2", auto) . 



lemma distR_match_grow_aux:"distR ls3 ls4 \<subseteq> distR ls1 ls2 \<Longrightarrow>
ls1 \<subset> ls3 \<Longrightarrow>ls2 \<subset> ls4 \<Longrightarrow>
        distR (insert a ls3) (insert b ls4)
     \<subseteq> distR (insert a ls1) (insert b ls2)"

unfolding distR_def
  apply (cases "a=b")
  subgoal by blast
  subgoal
    apply (cases "b \<in> ls2")  
      apply (cases "a \<in> ls2")
    by (cases "a \<in> ls4", auto) .

lemma distL_match_grow: "distL ls3 ls4 \<subseteq> distL ls1 ls2 \<Longrightarrow>
ls1 \<subseteq> ls3 \<Longrightarrow>ls2 \<subseteq> ls4 \<Longrightarrow> (ls1 = ls3 \<longleftrightarrow> ls2 = ls4) \<Longrightarrow>
        distL (insert a ls3) (insert b ls4)
     \<subseteq> distL (insert a ls1) (insert b ls2)"
  apply(cases "ls1 = ls3")
  subgoal by (metis Diff_mono Set.insert_mono distL_def)
  subgoal apply(cases "ls2 = ls4") by (simp add: distL_match_grow_aux)+ .


lemma distR_match_grow:"distR ls3 ls4 \<subseteq> distR ls1 ls2 \<Longrightarrow>
ls1 \<subseteq> ls3 \<Longrightarrow>ls2 \<subseteq> ls4 \<Longrightarrow> (ls1 = ls3 \<longleftrightarrow> ls2 = ls4) \<Longrightarrow>
        distR (insert a ls3) (insert b ls4)
     \<subseteq> distR (insert a ls1) (insert b ls2)"
  apply(cases "ls1 = ls3")
  subgoal by (metis Diff_mono Set.insert_mono distR_def)
  subgoal apply(cases "ls2 = ls4") by (simp add: distR_match_grow_aux)+ .

definition Dist where "Dist ls1 ls2 ls3 ls4 =
 (Language_Prelims.dist ls3 ls4 \<subseteq> Language_Prelims.dist ls1 ls2 \<and> ls1 \<subseteq> ls3 \<and> ls2 \<subseteq> ls4)"

lemmas Dist_defs = Dist_def dist_def

lemma Dist_neq[simp]:"Dist ls1 ls2 ls3 ls4 \<Longrightarrow> ls3 \<noteq> ls4 \<Longrightarrow> ls1 \<noteq> ls2"
  unfolding Dist_def by auto

lemma Dist_eq[simp]:"Dist A B A B" by (simp add: Dist_def)
(*istate*)
lemma Dist_emp[simp]:"Dist {} {} {} {}" by (simp add: Dist_def)

(*for match*)
lemma Dist_match[intro]:"Dist ls1 ls2 ls3 ls4 \<Longrightarrow> Dist (insert a ls1) (insert b ls2) (insert a ls3) (insert b ls4)"
  by (metis Dist_def Set.insert_mono dist_match_grow_diff1)

lemma Dist_match_un[intro]:"Dist ls1 ls2 ls3 ls4 \<Longrightarrow> Dist (ls1 \<union> a) (ls2 \<union> b) (ls3 \<union> a) (ls4 \<union> b)"
  unfolding Dist_def by (metis dist_eq_grow_ab subset_refl sup_mono)

(*for ignore*)
lemma Dist_ignore[intro]:"Dist ls1 ls2 ls3 ls4 \<Longrightarrow> Dist ls1 ls2 (insert a ls3) (insert a ls4)"
  by (meson Dist_def dist_insert_su dual_order.trans subset_insertI)

lemma Dist_ignore_un[intro]:"Dist ls1 ls2 ls3 ls4 \<Longrightarrow> Dist ls1 ls2 (ls3 \<union> a) (ls4 \<union> a)"
  unfolding Dist_def by (simp add: dist_ignore_grow le_supI1)

(* Various reflexive-transitive closure operators *)

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

hide_fact (open) refl step  \<comment> \<open>names too generic\<close>

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof(induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
  star.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

lemmas star_induct4 =
  star.induct[of "r:: 'a*'b'*'c*'d \<Rightarrow> 'a*'b'*'c*'d \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
by(metis star.refl star.step)

code_pred star .

(* *)

inductive
  starn :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "starn r 0 x x" |
step:  "r x y \<Longrightarrow> starn r n y z \<Longrightarrow> starn r (Suc n)x z"

hide_fact (open) refl step  \<comment> \<open>names too generic\<close>

lemma starn_trans:
  "starn r m x y \<Longrightarrow> starn r n y z \<Longrightarrow> starn r (m+n) x z"
proof(induction rule: starn.induct)
  case refl thus ?case by simp
next
  case step thus ?case by simp (metis starn.step)
qed

lemmas starn_induct =
  starn.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare starn.refl[simp,intro]

lemma starn_step1[simp, intro]: "r x y \<Longrightarrow> starn r (Suc 0) x y"
by(metis starn.refl starn.step)

code_pred starn .

lemma star_starn: "star r x y \<Longrightarrow> \<exists>n. starn r n x y"
by (induct rule: star.induct, auto intro: starn.intros)

lemma starn_star: "starn r n x y \<Longrightarrow> star r x y"
by (induct rule: starn.induct, auto intro: star.intros)

lemma star_iff_starn: "star r x y \<longleftrightarrow> (\<exists>n. starn r n x y)"
by (meson star_starn starn_star)

(* *)

inductive
  starl :: "('a \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'c list \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "starl r x [] x" |
step:  "r x c y \<Longrightarrow> starl r y cs z \<Longrightarrow> starl r x (c#cs) z"

hide_fact (open) refl step  \<comment> \<open>names too generic\<close>

lemma starl_trans:
  "starl r x cs y \<Longrightarrow> starl r y ds z \<Longrightarrow> starl r x (cs @ ds) z"
proof(induction rule: starl.induct)
  case refl thus ?case by simp
next
  case step thus ?case by simp (metis starl.step)
qed

lemmas starl_induct =
  starl.induct[of "r:: 'a*'b \<Rightarrow> 'clist \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare starl.refl[simp,intro]

lemma starl_step1[simp, intro]: "r x c y \<Longrightarrow> starl r x [c] y"
by(metis starl.refl starl.step)

lemma starl_snoc:
  "starl r x cs y \<Longrightarrow> r y c z \<Longrightarrow> starl r x (cs @ [c]) z"
by (simp add: starl_trans)

code_pred starl .

definition "final r x \<equiv> \<forall>y. \<not> r x y"

lemma final_star_eq: "final r x \<Longrightarrow> star r x y \<Longrightarrow> x = y"
by (metis final_def star.cases)

definition "lfinal r x \<equiv> \<forall>y cs. \<not> r x cs y"


end 