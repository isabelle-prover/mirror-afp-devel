(*
Boolean Expression Checkers Based on Binary Decision Trees
Author: Tobias Nipkow
*)

theory Boolean_Expression_Checkers
imports Main
begin

section{* Tautology (etc) Checking via Binary Decision Trees *}

subsection {* Boolean Expressions *}

text{* This is the interface to the tautology checker. If you have your own
type of boolean expressions you need to translate into this type first. *}

datatype 'a bool_expr =
  Const_bool_expr bool |
  Atom_bool_expr 'a |
  Neg_bool_expr "'a bool_expr" |
  And_bool_expr "'a bool_expr" "'a bool_expr" |
  Or_bool_expr "'a bool_expr" "'a bool_expr" |
  Imp_bool_expr "'a bool_expr" "'a bool_expr" |
  Iff_bool_expr "'a bool_expr" "'a bool_expr"

primrec val_bool_expr :: "'a bool_expr \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"val_bool_expr (Const_bool_expr b) s = b" |
"val_bool_expr (Atom_bool_expr x)   s = s x" |
"val_bool_expr (Neg_bool_expr b)   s = (\<not> val_bool_expr b s)" |
"val_bool_expr (And_bool_expr b1 b2) s = (val_bool_expr b1 s \<and> val_bool_expr b2 s)" |
"val_bool_expr (Or_bool_expr b1 b2) s = (val_bool_expr b1 s \<or> val_bool_expr b2 s)" |
"val_bool_expr (Imp_bool_expr b1 b2) s = (val_bool_expr b1 s \<longrightarrow> val_bool_expr b2 s)" |
"val_bool_expr (Iff_bool_expr b1 b2) s = (val_bool_expr b1 s = val_bool_expr b2 s)"


subsection{* Binary Decision Trees *}

datatype 'a ifex = Trueif | Falseif | IF 'a "'a ifex" "'a ifex"

fun val_ifex :: "'a ifex \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"val_ifex Trueif s = True" |
"val_ifex Falseif s = False" |
"val_ifex (IF n t1 t2) s = (if s n then val_ifex t1 s else val_ifex t2 s)"


subsection{* A Simple Minded Translation *}

text {* Simple minded normalisation, can create branches with repeated vars: *}

primrec normif0 :: "'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
"normif0 Trueif t1 t2 = t1" |
"normif0 Falseif t1 t2 = t2" |
"normif0 (IF x t1 t2) t3 t4 = IF x (normif0 t1 t3 t4) (normif0 t2 t3 t4)"

text {* The corresponding translation from boolean expressions to if-expressions: *}

primrec ifex0 :: "'a bool_expr \<Rightarrow> 'a ifex" where
"ifex0 (Const_bool_expr b) = (if b then Trueif else Falseif)" |
"ifex0 (Atom_bool_expr x)   = IF x Trueif Falseif" |
"ifex0 (Neg_bool_expr b)   = normif0 (ifex0 b) Falseif Trueif" |
"ifex0 (And_bool_expr b1 b2) = normif0 (ifex0 b1) (ifex0 b2) Falseif" |
"ifex0 (Or_bool_expr b1 b2) = normif0 (ifex0 b1) Trueif (ifex0 b2)" |
"ifex0 (Imp_bool_expr b1 b2) = normif0 (ifex0 b1) (ifex0 b2) Trueif" |
"ifex0 (Iff_bool_expr b1 b2) = (let t1 = ifex0 b1; t2 = ifex0 b2 in
   normif0 t1 t2 (normif0 t2 Falseif Trueif))"

lemma val_normif0:
  "val_ifex (normif0 t t1 t2) s = val_ifex (if val_ifex t s then t1 else t2) s"
by(induct t arbitrary: t1 t2) auto

theorem val_ifex0: "val_ifex (ifex0 b) = val_bool_expr b"
by(induct_tac b)(auto simp: val_normif0 Let_def)


subsection{* Translation to Reduced Binary Decision Trees *}

text {* An improved translation. *}

subsubsection{* Environment *}

text{* Environments are substitutions of values for variables: *}

type_synonym 'a env_bool = "('a * bool) list"

definition agree :: "('a \<Rightarrow> bool) \<Rightarrow> 'a env_bool \<Rightarrow> bool" where
"agree s env = (\<forall>x b. map_of env x = Some b \<longrightarrow> s x = b)"

lemma agree_Nil: "agree s []"
by(simp add: agree_def)

lemma agree_Cons: "distinct(map fst env) \<Longrightarrow> x \<notin> set(map fst env)
  \<Longrightarrow> agree s ((x,b) # env) = ((if b then s x else \<not> s x) \<and> agree s env)"
by(auto simp: agree_def image_iff)

lemma agreeDT:
  "\<lbrakk> agree s env; distinct (map fst env) \<rbrakk> \<Longrightarrow> (x,True) \<in> set env \<Longrightarrow> s x"
by(simp add: agree_def)

lemma agreeDF:
  "\<lbrakk> agree s env; distinct (map fst env) \<rbrakk> \<Longrightarrow> (x,False) \<in> set env \<Longrightarrow> \<not> s x"
by(simp add: agree_def)

subsubsection{* Translation and Normalisation *}

text {* A normalisation avoiding duplicate variables and collapsing
  @{term "If x t t"} to @{text t}. *}

definition mkIF :: "'a \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
"mkIF x t1 t2 = (if t1=t2 then t1 else IF x t1 t2)"

fun reduce :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
"reduce env (IF x t1 t2) = (case map_of env x of
     None \<Rightarrow> mkIF x (reduce ((x,True)#env) t1) (reduce ((x,False)#env) t2) |
     Some b \<Rightarrow> reduce env (if b then t1 else t2))" |
"reduce _ t = t"

primrec normif :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" where
"normif env Trueif t1 t2 = reduce env t1" |
"normif env Falseif t1 t2 = reduce env t2" |
"normif env (IF x t1 t2) t3 t4 =
  (case map_of env x of
     None \<Rightarrow> mkIF x (normif ((x,True)#env) t1 t3 t4) (normif ((x,False)#env) t2 t3 t4) |
     Some b \<Rightarrow> if b then normif env t1 t3 t4 else normif env t2 t3 t4)"

primrec ifex_of :: "'a bool_expr \<Rightarrow> 'a ifex" where
"ifex_of (Const_bool_expr b) = (if b then Trueif else Falseif)" |
"ifex_of (Atom_bool_expr x)   = IF x Trueif Falseif" |
"ifex_of (Neg_bool_expr b)   = normif [] (ifex_of b) Falseif Trueif" |
"ifex_of (And_bool_expr b1 b2) = normif [] (ifex_of b1) (ifex_of b2) Falseif" |
"ifex_of (Or_bool_expr b1 b2) = normif [] (ifex_of b1) Trueif (ifex_of b2)" |
"ifex_of (Imp_bool_expr b1 b2) = normif [] (ifex_of b1) (ifex_of b2) Trueif" |
"ifex_of (Iff_bool_expr b1 b2) = (let t1 = ifex_of b1; t2 = ifex_of b2 in
   normif [] t1 t2 (normif [] t2 Falseif Trueif))"

subsubsection{* Functional Correctness Proof *}

lemma val_mkIF: "val_ifex (mkIF x t1 t2) s = val_ifex (IF x t1 t2) s"
by(auto simp: mkIF_def Let_def)

theorem val_reduce: "agree s env \<Longrightarrow> distinct(map fst env) \<Longrightarrow>
  val_ifex (reduce env t) s = val_ifex t s"
apply(induct t arbitrary: s env)
apply(auto simp: map_of_eq_None_iff val_mkIF agree_Cons Let_def
  dest: agreeDT agreeDF split: option.splits)
done

lemma val_normif: "agree s env \<Longrightarrow> distinct(map fst env) \<Longrightarrow>
  val_ifex (normif env t t1 t2) s =
  val_ifex (if val_ifex t s then t1 else t2) s"
apply(induct t arbitrary: t1 t2 s env)
apply(auto simp: val_reduce val_mkIF agree_Cons map_of_eq_None_iff
  dest: agreeDT agreeDF split: option.splits)
done

theorem val_ifex: "val_ifex (ifex_of b) s = val_bool_expr b s"
by(induct_tac b)(auto simp: val_normif agree_Nil Let_def)

subsubsection{* A Tautology Checker for Arbitrary If-Expressions *}

text{* Not really needed because @{const ifex_of} produces reduced
expressions which can be checked very easily. *}

fun taut_test_rec :: "'a ifex \<Rightarrow> 'a env_bool \<Rightarrow> bool" where
"taut_test_rec Trueif env = True" |
"taut_test_rec Falseif env = False" |
"taut_test_rec (IF x t1 t2) env = (case map_of env x of
  Some b \<Rightarrow> taut_test_rec (if b then t1 else t2) env |
  None \<Rightarrow> taut_test_rec t1 ((x,True)#env) \<and> taut_test_rec t2 ((x,False)#env))"

lemma taut_test_rec: "distinct(map fst env)
  \<Longrightarrow> taut_test_rec t env = (\<forall>s. agree s env \<longrightarrow> val_ifex t s)"
proof(induct t arbitrary: env)
  case Trueif thus ?case by simp
next
  case Falseif
  have "agree (\<lambda>x. the(map_of env x)) env" by(auto simp: agree_def)
  thus ?case by(auto)
next
  case (IF x t1 t2) show ?case
  proof (cases "map_of env x")
    case None thus ?thesis using IF
      by (simp) (auto simp: map_of_eq_None_iff image_iff agree_Cons)
  next
    case Some thus ?thesis using IF
      by (simp add: agree_def)
  qed
qed

definition taut_test_ifex :: "'a ifex \<Rightarrow> bool" where
"taut_test_ifex t = taut_test_rec t []"

corollary taut_test_ifex: "taut_test_ifex t = (\<forall>s. val_ifex t s)"
using taut_test_rec[of "[]" t]
by (auto simp: val_ifex taut_test_ifex_def agree_Nil)

subsubsection{* Reduced If-Expressions *}

text{* Proof that the result of @{const ifex_of} is reduced.
An expression reduced iff no variable appears twice on any branch and
there is no subexpression @{term"IF x t t"}. *}

fun reduced :: "'a ifex \<Rightarrow> 'a set \<Rightarrow> bool" where
"reduced (IF x t1 t2) X =
  (x \<notin> X \<and> t1 \<noteq> t2 \<and> reduced t1 (insert x X) \<and> reduced t2 (insert x X))" |
"reduced _ _ = True"

lemma reduced_antimono: "X \<subseteq> Y \<Longrightarrow> reduced t Y \<Longrightarrow> reduced t X"
apply(induction t arbitrary: X Y)
by auto (metis insert_mono)+

lemma reduced_mkIF: "x \<notin> X \<Longrightarrow>
  reduced t1 (insert x X) \<Longrightarrow> reduced t2 (insert x X) \<Longrightarrow> reduced (mkIF x t1 t2) X"
by(auto simp: mkIF_def intro:reduced_antimono)

lemma reduced_reduce:
  "distinct(map fst env) \<Longrightarrow> reduced (reduce env t) (fst ` set env)"
proof(induction t arbitrary: env)
  case (IF x t1 t2)
  thus ?case using IF.IH(1)[of "(x, True) # env"] IF.IH(2)[of "(x, False) # env"]
    by(auto simp: map_of_eq_None_iff image_iff reduced_mkIF split: option.split)
qed auto

lemma reduced_normif:
  "distinct(map fst env) \<Longrightarrow> reduced (normif env t t1 t2) (fst ` set env)"
proof(induction t arbitrary: t1 t2 env)
  case (IF x s1 s2)
  thus ?case using IF.IH(1)[of "(x, True) # env"] IF.IH(2)[of "(x, False) # env"]
    by(auto simp: reduced_mkIF map_of_eq_None_iff split: option.split)
qed (auto simp: reduced_reduce)

theorem reduced_ifex: "reduced (ifex_of b) {}"
by(induct b)(auto simp: reduced_normif[of "[]", simplified] Let_def)

text{* Proof that reduced if-expressions are @{const Trueif}, @{const Falseif}
or can evaluate to both @{const True} and @{const False}. *}

lemma same_val_if_reduced:
  "reduced t X \<Longrightarrow> \<forall>x. x \<notin> X \<longrightarrow> s1 x = s2 x \<Longrightarrow> val_ifex t s1 = val_ifex t s2"
by(induction t arbitrary: X) auto

lemma reduced_IF_depends: "\<lbrakk> reduced t X; t \<noteq> Trueif; t \<noteq> Falseif \<rbrakk>
  \<Longrightarrow> \<exists>s1 s2. val_ifex t s1 \<noteq> val_ifex t s2"
proof(induction t arbitrary: X)
  case (IF x t1 t2)
  let ?t = "IF x t1 t2"
  have 1: "reduced t1 (insert x X)" using IF.prems(1) by simp
  have 2: "reduced t2 (insert x X)" using IF.prems(1) by simp
  show ?case
  proof(cases t1)
    case [simp]: Trueif
    show ?thesis
    proof (cases t2)
      case Trueif thus ?thesis using IF.prems(1) by simp
    next
      case Falseif
      hence "val_ifex ?t (\<lambda>_. True) \<noteq> val_ifex ?t (\<lambda>_. False)" by simp
      thus ?thesis by blast
    next
      case IF
      then obtain s1 s2 where "val_ifex t2 s1 \<noteq> val_ifex t2 s2"
        using IF.IH(2)[OF 2] IF.prems(1) by auto
      hence "val_ifex ?t (s1(x:=False)) \<noteq> val_ifex ?t (s2(x:=False))"
        using same_val_if_reduced[OF 2, of "s1(x:=False)" s1]
          same_val_if_reduced[OF 2, of "s2(x:=False)" s2] by simp
      thus ?thesis by blast
    qed
  next
    case [simp]: Falseif
    show ?thesis
    proof (cases t2)
      case Falseif thus ?thesis using IF.prems(1) by simp
    next
      case Trueif
      hence "val_ifex ?t (\<lambda>_. True) \<noteq> val_ifex ?t (\<lambda>_. False)" by simp
      thus ?thesis by blast
    next
      case IF
      then obtain s1 s2 where "val_ifex t2 s1 \<noteq> val_ifex t2 s2"
        using IF.IH(2)[OF 2] IF.prems(1) by auto
      hence "val_ifex ?t (s1(x:=False)) \<noteq> val_ifex ?t (s2(x:=False))"
        using same_val_if_reduced[OF 2, of "s1(x:=False)" s1]
          same_val_if_reduced[OF 2, of "s2(x:=False)" s2] by simp
      thus ?thesis by blast
    qed
  next
    case IF
    then obtain s1 s2 where "val_ifex t1 s1 \<noteq> val_ifex t1 s2"
      using IF.IH(1)[OF 1] IF.prems(1) by auto
    hence "val_ifex ?t (s1(x:=True)) \<noteq> val_ifex ?t (s2(x:=True))"
      using same_val_if_reduced[OF 1, of "s1(x:=True)" s1]
          same_val_if_reduced[OF 1, of "s2(x:=True)" s2] by simp
    thus ?thesis by blast
  qed
qed auto


subsection{* Tautology Checking *}

definition taut_test :: "'a bool_expr \<Rightarrow> bool" where
"taut_test b = (ifex_of b = Trueif)"

corollary taut_test: "taut_test b = (\<forall>s. val_bool_expr b s)"
unfolding taut_test_def using reduced_IF_depends[OF reduced_ifex, of b]
by (metis val_ifex val_ifex.simps)


subsection{* Satisfiability Checking *}

definition sat_test :: "'a bool_expr \<Rightarrow> bool" where
"sat_test b = (ifex_of b \<noteq> Falseif)"

corollary sat_test: "sat_test b = (\<exists>s. val_bool_expr b s)"
unfolding sat_test_def using reduced_IF_depends[OF reduced_ifex, of b]
by (metis val_ifex val_ifex.simps(1) val_ifex.simps(2))


subsection{* Equivalence Checking *}

definition equiv_test :: "'a bool_expr \<Rightarrow> 'a bool_expr \<Rightarrow> bool" where
"equiv_test b1 b2 = taut_test (Iff_bool_expr b1 b2)"

corollary equiv_test: "equiv_test b1 b2 = (\<forall>s. val_bool_expr b1 s = val_bool_expr b2 s)"
by(auto simp:equiv_test_def taut_test)


text{* Hide everything except the boolean expressions and the checkers. *}

hide_type (open) ifex env_bool
hide_const (open)  Trueif Falseif IF val_ifex normif0 ifex0 agree mkIF
  reduce normif ifex_of reduced taut_test_rec taut_test_ifex

end
