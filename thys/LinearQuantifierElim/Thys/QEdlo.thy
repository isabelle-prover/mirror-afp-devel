(*  ID:         $Id: QEdlo.thy,v 1.2 2008-01-11 15:22:19 lsf37 Exp $
    Author:     Tobias Nipkow, 2007
*)

theory QEdlo
imports DLO "~~/src/HOL/ex/Reflection"
begin

subsection "DNF-based quantifier elimination"

definition qe_less :: "atom list \<Rightarrow> atom fm" where
"qe_less as =
 (if Less 0 0 \<in> set as then FalseF else
  let lbs = [i. Less (Suc i) 0 \<leftarrow> as]; ubs = [j. Less 0 (Suc j) \<leftarrow> as];
      pairs = [Atom(Less i j). i \<leftarrow> lbs, j \<leftarrow> ubs]
  in list_conj pairs)"

theorem I_qe_less:
assumes less: "\<forall>a \<in> set as. is_Less a" and dep: "\<forall>a \<in> set as. depends\<^isub>d\<^isub>l\<^isub>o a"
shows "DLO.I (qe_less as) xs = (\<exists>x. \<forall>a \<in> set as. I\<^isub>d\<^isub>l\<^isub>o a (x#xs))"
  (is "?L = ?R")
proof
  let ?lbs = "[i. Less (Suc i) 0 \<leftarrow> as]"
  let ?ubs = "[j. Less 0 (Suc j) \<leftarrow> as]"
  let ?Ls = "set ?lbs" let ?Us = "set ?ubs"
  let ?lb = "Max (\<Union>x\<in>?Ls. {xs!x})"
  let ?ub = "Min (\<Union>x\<in>?Us. {xs!x})"
  have 2: "Less 0 0 \<notin> set as \<Longrightarrow> \<forall>a \<in> set as.
      (\<exists>i \<in> ?Ls. a = Less (Suc i) 0) \<or> (\<exists>i \<in> ?Us. a = Less 0 (Suc i))"
  proof
    fix a assume "Less 0 0 \<notin> set as" "a \<in> set as"
    then obtain i j where [simp]: "a = Less i j"
      using less by (force simp:is_Less_iff)
    with dep obtain k where "i = 0 \<and> j = Suc k \<or> i = Suc k \<and> j = 0"
      using `Less 0 0 \<notin> set as` `a \<in> set as`
      by auto (metis Nat.nat.nchotomy depends\<^isub>d\<^isub>l\<^isub>o.simps(2))
    moreover hence "i=0 \<and> k \<in> ?Us \<or> j=0 \<and> k \<in> ?Ls"
      using `a \<in> set as` by force
    ultimately show "(\<exists>i\<in>?Ls. a=Less (Suc i) 0) \<or> (\<exists>i\<in>?Us. a=Less 0 (Suc i))"
      by force
  qed
  assume qe1: ?L
  hence 0: "Less 0 0 \<notin> set as" by (auto simp:qe_less_def)
  with qe1 have 1: "\<forall>x\<in>?Ls. \<forall>y\<in>?Us. xs ! x < xs ! y"
    by (fastsimp simp:qe_less_def)
  { fix i x
    assume "Less i 0 \<in> set as | Less 0 i \<in> set as"
    moreover hence "i \<noteq> 0" using 0 by iprover
    ultimately have "(x#xs) ! i = xs!(i - 1)" by (simp add: nth_Cons')
  } note this[simp]
  { assume nonempty: "?Ls \<noteq> {} \<and> ?Us \<noteq> {}"
    hence "Max (\<Union>x\<in>?Ls. {xs!x}) < Min (\<Union>x\<in>?Us. {xs!x})"
      using 1 by(simp)
    then obtain m where "?lb < m \<and> m < ?ub" using dense by blast
    hence "\<forall>i\<in>?Ls. xs!i < m" and "\<forall>j\<in>?Us. m < xs!j"
      using nonempty by auto
    hence "\<forall>a \<in> set as. I\<^isub>d\<^isub>l\<^isub>o a (m # xs)" using 2[OF 0] by(auto simp:less)
    hence ?R .. }
  moreover
  { assume asm: "?Ls \<noteq> {} \<and> ?Us = {}"
    then obtain m where "?lb < m" using no_ub by blast
    hence "\<forall>a\<in> set as. I\<^isub>d\<^isub>l\<^isub>o a (m # xs)" using 2[OF 0] asm by auto
    hence ?R .. }
  moreover
  { assume asm: "?Ls = {} \<and> ?Us \<noteq> {}"
    then obtain m where "m < ?ub" using no_lb by blast
    hence "\<forall>a\<in> set as. I\<^isub>d\<^isub>l\<^isub>o a (m # xs)" using 2[OF 0] asm by auto
    hence ?R .. }
  moreover
  { assume "?Ls = {} \<and> ?Us = {}"
    hence ?R using 2[OF 0] by (auto simp add:less)
  }
  ultimately show ?R by blast
next
  assume ?R
  then obtain x where 1: "\<forall>a\<in> set as. I\<^isub>d\<^isub>l\<^isub>o a (x # xs)" ..
  hence 0: "Less 0 0 \<notin> set as" by auto
  { fix i j
    assume asm: "Less i 0 \<in> set as" "Less 0 j \<in> set as"
    hence "(x#xs)!i < x" "x < (x#xs)!j" using 1 by auto+
    hence "(x#xs)!i < (x#xs)!j" by(rule order_less_trans)
    moreover have "\<not>(i = 0 | j = 0)" using 0 asm by blast
    ultimately have "xs ! (i - 1) < xs ! (j - 1)" by (simp add: nth_Cons')
  }
  thus ?L using 0 less
    by (fastsimp simp: qe_less_def is_Less_iff split:atom.splits nat.splits)
qed

lemma I_qe_less_pretty:
  "\<forall>a \<in> set as. is_Less a \<and> depends\<^isub>d\<^isub>l\<^isub>o a \<Longrightarrow> DLO.is_dnf_qe _ qe_less as"
by(metis I_qe_less)

definition subst :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"subst i j k = (if k=0 then if i=0 then j else i else k) - 1"
fun subst\<^isub>0 :: "atom \<Rightarrow> atom \<Rightarrow> atom" where
"subst\<^isub>0 (Eq i j) a = (case a of
   Less m n \<Rightarrow> Less (subst i j m) (subst i j n)
 | Eq m n \<Rightarrow> Eq (subst i j m) (subst i j n))"

lemma subst\<^isub>0_pretty:
  "subst\<^isub>0 (Eq i j) (Less m n) = Less (subst i j m) (subst i j n)"
  "subst\<^isub>0 (Eq i j) (Eq m n) = Eq (subst i j m) (subst i j n)"
by auto

(*<*)
(* needed for code generation *)
definition [code func del]: "lift_dnfeq_qe = ATOM_EQ.lift_dnfeq_qe neg\<^isub>d\<^isub>l\<^isub>o depends\<^isub>d\<^isub>l\<^isub>o decr\<^isub>d\<^isub>l\<^isub>o (\<lambda>Eq i j \<Rightarrow> i=0 \<or> j=0 | a \<Rightarrow> False)
          (\<lambda>Eq i j \<Rightarrow> i=j | a \<Rightarrow> False) subst\<^isub>0"
definition [code func del]:
  "lift_eq_qe = ATOM_EQ.lift_eq_qe (\<lambda>Eq i j \<Rightarrow> i=0 \<or> j=0 | a \<Rightarrow> False)
                                   (\<lambda>Eq i j \<Rightarrow> i=j | a \<Rightarrow> False) subst\<^isub>0"

lemmas DLOe_code_lemmas = DLO_code_lemmas lift_dnfeq_qe_def lift_eq_qe_def

hide const lift_dnfeq_qe lift_eq_qe
(*>*)

interpretation DLO\<^isub>e:
  ATOM_EQ[neg\<^isub>d\<^isub>l\<^isub>o "(\<lambda>a. True)" I\<^isub>d\<^isub>l\<^isub>o depends\<^isub>d\<^isub>l\<^isub>o decr\<^isub>d\<^isub>l\<^isub>o
          "(\<lambda>Eq i j \<Rightarrow> i=0 \<or> j=0 | a \<Rightarrow> False)"
          "(\<lambda>Eq i j \<Rightarrow> i=j | a \<Rightarrow> False)" subst\<^isub>0]
apply(unfold_locales)
apply(fastsimp simp:subst_def nth_Cons' split:atom.splits split_if_asm)
apply(simp add:subst_def split:atom.splits)
apply(fastsimp simp:subst_def nth_Cons' split:atom.splits)
apply(fastsimp simp add:subst_def split:atom.splits)
done

(*<*)
lemmas [folded DLOe_code_lemmas, code] =
  DLO\<^isub>e.lift_dnfeq_qe_def DLO\<^isub>e.lift_eq_qe_def
(*>*)

setup {* Sign.revert_abbrev "" @{const_name DLO\<^isub>e.lift_dnfeq_qe} *}

definition "dlo_qe = DLO\<^isub>e.lift_dnfeq_qe qe_less"
(*<*)
lemmas [folded DLOe_code_lemmas, code] = dlo_qe_def 
(*>*)

lemma qfree_qe_less: "qfree (qe_less as)"
by(auto simp:qe_less_def intro!:qfree_list_conj)

theorem I_dlo_qe: "DLO.I (dlo_qe \<phi>) xs = DLO.I \<phi> xs"
unfolding dlo_qe_def
by(fastsimp intro!: I_qe_less qfree_qe_less DLO\<^isub>e.I_lift_dnfeq_qe
        simp: is_Less_iff not_is_Eq_iff split:atom.splits cong:conj_cong)

theorem qfree_dlo_qe: "qfree (dlo_qe \<phi>)"
by(simp add:dlo_qe_def DLO\<^isub>e.qfree_lift_dnfeq_qe qfree_qe_less)

end
