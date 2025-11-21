(* Title:      	   Abstract Queue Lock
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Ticket Lock\<close>

theory Function_Supplementary

imports Main

begin

text \<open>This theory contains some function-related definitions and associated
lemmas that are not included in the built-in library. They are grouped into
two sections:

\begin{enumerate}

\item
Predicates that describe functions that are injective or surjective when
restricted to subsets of their domains or images.

\item
A higher-order function that performs a list of updates on a function.

\end{enumerate}

The content of this theory was conceived during a project on formal program
verification of locks (i.e. mutexes). The new definitions and lemmas arose 
from the proof of data refinement from an abstract queue-lock to a ticket-lock.

Inspired by the theories \emph{List Index} (Nipkow 2010) and \emph{Fixed-Length
Vectors} (Hupel 2023) on the Archive of Formal Proofs, we hope that these new
definitions and lemmas may also be of help to others.\<close>

(*==================================================================*)
subsection \<open>Helpers: Inj, Surj and Bij\<close>

text \<open>It is sometimes useful to describe a function that is not injective in
itself, but is injective when its image is restricted to a subset.

For example, consider the function $\{ a \mapsto 1, b \mapsto 2, c \mapsto 2 \}$.
This function is not injective, but if its image is restricted to $\{ 1 \}$,
the new function $\{ a \mapsto 1 \}$ becomes injective.

This motivates the following definition.\<close>

definition inj_img :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj_img f B \<equiv> \<forall> x1 x2. f x1 = f x2 \<and> f x1 \<in> B \<longrightarrow> x1 = x2"

text \<open>Similarly, the next definition describes a function that becomes
surjective when its codomain is restricted to a subset.

In other words, ``surj\_codom $f$ $B$'' means that \emph{every element in $B$
is mapped to by $f$}.

For example, consider the function that maps from the domain $\{ a, b \}$
to the codomain $\{ 1, 2 \}$ with the graph $\{ a \mapsto 1, b \mapsto 1 \}$.
This function is not surjective, but if its codomain is restricted to $\{ 1 \}$,
then the new function becomes surjective.\<close>

definition surj_codom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "surj_codom f B \<equiv> \<forall> y \<in> B. (\<exists> x. f x = y)"

text \<open>We can also describe a function that remains surjective on a subset
of its domain.

In other words, ``surj\_on $f$ $A$'' means that \emph{mappings that originate
from $A$ already span the entire codomain}.

 Note that this is a notion stronger than plain surjectivity,
which will be shown in the later subsection ``Surj-Related''.\<close>

definition surj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "surj_on f A \<equiv> \<forall> y. (\<exists> x \<in> A. f x = y)"

text \<open>Note that all three definitions above are most likely not
included in the built-in library, as suggested by the outputs of
the following search-commands.\<close>

find_consts name:"inj"
find_consts name:"surj"

(*------------------------------------------------------------------*)
subsubsection \<open>Inj-Related\<close>

lemma inj_implies_inj_on: "inj f \<Longrightarrow> inj_on f A"
  using inj_on_subset by blast

lemma inj_implies_inj_img: "inj f \<Longrightarrow> inj_img f B"
  by (simp add: injD inj_img_def)

lemma inj_img_empty: "inj_img f {}"
  by (fastforce simp: inj_img_def)

lemma inj_img_singleton: "\<forall> x. f x \<noteq> b \<Longrightarrow> inj_img f {b}"
  by (fastforce simp: inj_img_def)

lemma inj_img_subset:
  "\<lbrakk> inj_img f B ; B' \<subseteq> B \<rbrakk> \<Longrightarrow> inj_img f B'"
  by (fastforce simp: inj_img_def)

lemma inj_img_superset:
  "\<lbrakk> inj_img f B ; \<forall> x. f x \<notin> B' - B \<rbrakk> \<Longrightarrow> inj_img f B'"
  by (fastforce simp: inj_img_def)

lemma inj_img_not_mapped_to: "\<forall>x. f x \<notin> B \<Longrightarrow> inj_img f B"
  by (fastforce simp: inj_img_def)

lemma inj_img_add_one_extra:
  "\<lbrakk> inj_img f B ; \<forall> x. f x \<noteq> b \<rbrakk> \<Longrightarrow> inj_img f (B \<union> {b})"
  by (fastforce simp: inj_img_def)

lemma inj_img_union_1:
  "\<lbrakk> inj_img f B1 ; inj_img f B2 \<rbrakk> \<Longrightarrow> inj_img f (B1 \<union> B2)"
  by (fastforce simp: inj_img_def)

lemma inj_img_union_2:
  "\<lbrakk> inj_img f B1 ; \<forall> x. f x \<notin> B2 \<rbrakk> \<Longrightarrow> inj_img f (B1 \<union> B2)"
  by (simp add: inj_img_not_mapped_to inj_img_union_1)

lemma inj_img_fun_upd_notin:
  "\<lbrakk> inj_img f B ; \<forall> x. f x \<noteq> b \<rbrakk> \<Longrightarrow> inj_img (fun_upd f a b) B"
  by (fastforce simp: inj_img_def)

lemma inj_img_fun_upd_singleton:
  "\<forall> x. f x \<noteq> b \<Longrightarrow> inj_img (fun_upd f a b) {b}"
  by (simp add: inj_img_fun_upd_notin inj_img_singleton)

(*------------------------------------------------------------------*)
subsubsection \<open>Surj-Related\<close>

text \<open>Lemmas related to ``surj codom''.\<close>

lemma surj_implies_surj_codom: "surj f \<Longrightarrow> surj_codom f B"
  by (metis surjD surj_codom_def)

lemma surj_codom_triv: "surj_codom f (f ` A)"
  by (fastforce simp: surj_codom_def)

lemma surj_codom_univ: "surj_codom f UNIV = surj f"
  by (metis surj_codom_def surj_def UNIV_I)

lemma surj_codom_empty: "surj_codom f {}"
  by (fastforce simp: surj_codom_def)

lemma surj_codom_singleton: "b \<in> range f \<Longrightarrow> surj_codom f {b}"
  by (fastforce simp: surj_codom_def)

lemma surj_codom_subset:
  "\<lbrakk> surj_codom f B ; B' \<subseteq> B \<rbrakk> \<Longrightarrow> surj_codom f B'"
  by (fastforce simp: surj_codom_def)

lemma surj_codom_union:
  "\<lbrakk> surj_codom f B1 ; surj_codom f B2 \<rbrakk> \<Longrightarrow> surj_codom f (B1 \<union> B2)"
  by (fastforce simp: surj_codom_def)

text \<open>Lemmas related to ``surj on''.\<close>

lemma surj_on_implies_surj: "surj_on f A \<Longrightarrow> surj f"
  by (metis surj_def surj_on_def)

lemma surj_on_univ: "surj_on f UNIV = surj f"
  by (metis UNIV_I surjD surj_on_def surj_on_implies_surj)

lemma surj_on_never_emptyset: "\<not> surj_on f {}"
  by (fastforce simp: surj_on_def)

lemma surj_on_superset:
  "\<lbrakk> surj_on f A ; A \<subseteq> A' \<rbrakk> \<Longrightarrow> surj_on f A'"
  by (fastforce simp: surj_on_def)

lemma surj_on_union:
  "\<lbrakk> surj_on f A1 ; surj_on f A2 \<rbrakk> \<Longrightarrow> surj_on f (A1 \<union> A2)"
  by (fastforce simp: surj_on_superset)

(*------------------------------------------------------------------*)
subsubsection \<open>Bij and Inv\<close>

text \<open>This section relates the new definitions to the existing 
``bijective between'' and ``inverse'' definitions.\<close>

lemma bij_betw_implies_inj_img: "bij_betw f UNIV B \<Longrightarrow> inj_img f B"
  by (fastforce simp: bij_betw_def inj_implies_inj_img)

lemma bij_betw_implies_surj_codom: "bij_betw f A B \<Longrightarrow> surj_codom f B"
  by (fastforce intro: f_the_inv_into_f_bij_betw simp: surj_codom_def)

lemma bij_betw_implies_surj_on: "bij_betw f A UNIV \<Longrightarrow> surj_on f A"
  by (meson UNIV_I bij_betw_iff_bijections surj_on_def)

text \<open>Other lemmas\<close>

lemma bij_extension:
  assumes "a \<notin> A"
      and "b \<notin> B"
      and "bij_betw f A B"
    shows "bij_betw (fun_upd f a b) (A \<union> {a}) (B \<union> {b})"
  by (metis assms bij_betw_combine bij_betw_cong bij_betw_singleton_iff disjoint_insert(1)
            fun_upd_other fun_upd_same inf_bot_right)

lemma bij_remove_one:
  assumes "a \<in> A"
      and "bij_betw f A B"
    shows "bij_betw f (A - {a}) (B - {f a})"
  using assms by (fastforce simp: bij_betwE bij_betw_DiffI)

lemma set_remove_one_element:
  assumes "x \<notin> B"
      and "B \<subseteq> A"
      and "A - {x} \<subseteq> B"
    shows "A - {x} = B"
  using assms by blast

lemma inv_image_restrict_inj:
  assumes "bij_betw f A B"
      and "inj_img f B"
      and "f a \<in> B"
    shows "a \<in> inv f ` B"
  using assms by (fastforce simp: f_inv_into_f inj_img_def rev_image_eqI)

lemma inv_image_restrict:
  assumes "inj_on f A"
      and "f a \<in> B"
      and "\<forall>x. (f x \<in> B \<longrightarrow> x \<in> A)"
    shows "a \<in> inv f ` B"
  using assms by (fastforce simp: f_inv_into_f inj_onD rev_image_eqI)

lemma inv_image_restrict_neg:
  assumes "bij_betw f A B"
      and "f a \<notin> B"
      and "\<forall>x. (f x \<in> B \<longrightarrow> x \<in> A)"
    shows "a \<notin> inv f ` B"
  using assms apply clarsimp
  by (metis (mono_tags, lifting) f_inv_into_f f_the_inv_into_f_bij_betw range_eqI)

lemma inv_image_restrict_neg':
  assumes "surj_codom f B"
      and "f a \<notin> B"
      and "\<forall>x. (f x \<in> B \<longrightarrow> x \<in> A)"
    shows "a \<notin> inv f ` B"
  using assms
  by (fastforce simp: surj_codom_def f_inv_into_f rangeI)

lemma bij_betw_inv1: 
  assumes "bij_betw f A B"
      and "inj_img f B"
      and "f a \<in> B"
    shows "inv f (f a) = a"
  using assms by (fastforce simp: f_inv_into_f inj_img_def)

lemma bij_betw_inv2: 
  assumes "bij_betw f A B"
      and "b \<in> B"
    shows "f (inv f b) = b"
  by (metis assms bij_betw_imp_surj_on f_inv_into_f rangeI)

lemma surj_codom_inj_on_vimage_bij_betw:
  "\<lbrakk> surj_codom f B ; inj_on f (vimage f B) \<rbrakk> \<Longrightarrow> bij_betw f (vimage f B) B"
  apply (rule bij_betwI')
  by (fastforce simp: inj_onD surj_codom_def)+

(*==================================================================*)
subsection \<open>Helpers: Multi-Updates on Functions\<close>

fun fun_upd_list :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "fun_upd_list f [] = f"
| "fun_upd_list f (xy # xys) = fun_upd (fun_upd_list f xys) (fst xy) (snd xy)"

text \<open>This notion can also be defined following the @{text foldl} pattern,
although this alternative form is not used.\<close>

fun fun_upd_list_l :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "fun_upd_list_l f [] = f"
| "fun_upd_list_l f (xy # xys) = fun_upd_list_l (fun_upd f (fst xy) (snd xy)) xys"

text \<open>Examples of the two definitions above.\<close>

value "fun_upd_list   (\<lambda>x.0::nat) [(1::nat,1),(4,3),(6,6),(4,4)] 4"
value "fun_upd_list_l (\<lambda>x.0::nat) [(1::nat,1),(4,3),(6,6),(4,4)] 4"

text \<open>Both definitions above resemble "folds" with some un-currying,
as shown by the following two lemmas.\<close>

lemma fun_upd_list_is_foldr:
  "fun_upd_list f0 pairs = foldr (\<lambda> pair f. fun_upd f (fst pair) (snd pair)) pairs f0"
  by (induct pairs; fastforce) 

lemma fun_upd_list_l_is_foldl:
  "fun_upd_list_l f0 pairs = foldl (\<lambda> f pair. f(fst pair := snd pair)) f0 pairs"
  by (induct pairs arbitrary: f0; force)

text \<open>These two definitions are equivalent when every domain-value is 
updated at most once.\<close>

lemma fun_upd_list_l_distinct_rewrite:
  "distinct (map fst (xy # xys))
   \<Longrightarrow> fun_upd_list_l (fun_upd f (fst xy) (snd xy))  xys
     = fun_upd        (fun_upd_list_l f xys)        (fst xy) (snd xy)"
proof (induct xys arbitrary: xy f)
  case (Cons xy2 xys2)
  thus ?case
    by (metis (no_types, lifting) distinct_length_2_or_more fun_upd_list_l.simps(2) fun_upd_twist list.simps(9))
qed (fastforce)

lemma fun_upd_list_defs_distinct_equiv:
  "distinct (map fst pairs) \<Longrightarrow> fun_upd_list f pairs = fun_upd_list_l f pairs"
proof (induct pairs)
  case (Cons xy xys)
  thus ?case
    by (fastforce simp: fun_upd_list_l_distinct_rewrite)
qed (fastforce)

text \<open>Smaller propositions\<close>

lemma fun_upd_list_distinct_rewrite:
  "distinct (map fst (xy # xys))
   \<Longrightarrow> fun_upd_list (fun_upd f (fst xy) (snd xy))  xys
     = fun_upd      (fun_upd_list f xys)        (fst xy) (snd xy)"
  by (simp add: fun_upd_list_defs_distinct_equiv fun_upd_list_l_distinct_rewrite)

lemma fun_upd_list_hd_1:
  "fun_upd_list f (zip (x # xs) (y # ys)) x = y"
  by simp

lemma fun_upd_list_hd_2:
  "\<lbrakk> xs \<noteq> [] ; ys \<noteq> [] \<rbrakk> \<Longrightarrow> fun_upd_list f (zip xs ys) (hd xs) = hd ys"
  by (metis fun_upd_list_hd_1 list.collapse)

lemma fun_upd_list_not_hd:
  assumes "a \<noteq> x"
  shows "fun_upd_list f (zip (x # xs) (y # ys)) a = fun_upd_list f (zip xs ys) a"
  using assms by simp

lemma fun_upd_list_not_updated_map:
  assumes "a \<notin> set (map fst xys)"
    shows "fun_upd_list f xys a = f a"
  using assms by (induction xys, simp_all)

lemma fun_upd_list_not_updated_zip:
  assumes "a \<notin> set xs"
    shows "fun_upd_list f (zip xs ys) a = f a"
  by (metis assms fun_upd_list_not_updated_map in_set_takeD map_fst_zip_take)

(*------------------------------------------------------------------*)
subsubsection \<open>Ordering of Updates\<close>

text \<open>The next two lemmas shows that the ordering of the updates does not matter,
as long as the updates are distinct.\<close>

lemma fun_upd_list_distinct_reorder:
  assumes "distinct (map fst pairs)"
      and "ab \<in> set pairs"
    shows "fun_upd_list f pairs
          = (fun_upd_list f (remove1 ab pairs)) (fst ab := snd ab)"
using assms 
proof (induct pairs)
  case (Cons xy xys)
  thus ?case
  proof (cases "ab = xy")
    case True
    thus ?thesis by simp
  next
    case False (* interesting internal steps omitted below *)
    (* Note: here, reasoning from right to left is easier than from left to right. *)
    hence "(fun_upd_list f (remove1 ab (xy # xys))) (fst ab := snd ab)
              = fun_upd_list f (xy # xys)"
      using Cons.hyps Cons.prems by fastforce
    thus ?thesis by fastforce
  qed
qed (fastforce)

lemma fun_upd_list_distinct_reorder_general:
  assumes "distinct (map fst pairs1)"
      and "distinct (map fst pairs2)"
      and "set pairs1 = set pairs2"
    shows "fun_upd_list f pairs1 = fun_upd_list f pairs2"
using assms 
proof (induct pairs1 arbitrary: pairs2)
  case (Cons xy xys)
  hence "fun_upd_list f pairs2
          = (fun_upd_list f (remove1 xy pairs2))(fst xy := snd xy)"
    by (metis list.set_intros(1) fun_upd_list_distinct_reorder Cons.prems(2,3))
  also have "... = (fun_upd_list f xys)(fst xy := snd xy)"
    by (metis (mono_tags, lifting) Cons.hyps Cons.prems distinct_map distinct_remove1 list.simps(9) 
                                   remove1.simps(2) set_remove1_eq)
  also have "... = fun_upd_list f (xy # xys)"
    by simp
  ultimately show ?case 
    by presburger
qed (fastforce)

(*------------------------------------------------------------------*)
subsubsection \<open>Surjective\<close>

lemma helper_surj_zip_1:
  assumes "a \<in> set xs"
      and "length xs = length ys"
    shows "fun_upd_list f (zip xs ys) a \<in> set ys"
using assms 
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  thus ?case
    apply (cases "x = a")
     apply (metis Cons.prems(2) fun_upd_list_hd_1 length_0_conv list.distinct(1) list.exhaust_sel 
                  list.set_intros(1))
    by (metis Cons.IH Cons.prems(1,2) fun_upd_list_not_hd length_Suc_conv list.set_intros(2) set_ConsD)
qed (fastforce)

lemma fun_upd_list_surj_zip_1:
  assumes "length xs = length ys"
    shows "fun_upd_list f (zip xs ys) ` set xs \<subseteq> set ys"
  using assms helper_surj_zip_1 by force

lemma fun_upd_list_surj_map_1:
  "(fun_upd_list f xys) ` set (map fst xys) \<subseteq> set (map snd xys)"
  by (metis fun_upd_list_surj_zip_1 length_map zip_map_fst_snd)

lemma fun_upd_list_surj_map_2:
  assumes "distinct (map fst xys)"
    shows "set (map snd xys) \<subseteq> (fun_upd_list f xys) ` set (map fst xys)"
using assms proof (induct xys)
  case (Cons xy tail)
  { fix b assume assms_b: "b \<in> set (map snd (xy # tail))"
    hence "\<exists> a \<in> set (map fst (xy # tail)). (fun_upd_list f (xy # tail)) a = b"
    proof (cases "b = snd xy")
      case True
      show ?thesis using True by simp
    next
      case False
      hence 2: "\<exists> a \<in> set (map fst tail). (fun_upd_list f tail) a = b"
        using Cons assms_b by fastforce
      { fix aa assume 3: "aa \<in> set (map fst tail) \<and> (fun_upd_list f tail) aa = b"
        from 3 have 5: "(fun_upd_list f (xy # tail)) aa = b"
          using fun_upd_list_not_hd Cons.prems
          by (metis (no_types, lifting) distinct.simps(2) list.simps(9) zip_map_fst_snd)
        from 5 have ?thesis 
          by (metis 3 list.set_intros(2) list.simps(9)) 
      }
      thus ?thesis using 2 by blast
    qed }
  thus ?case by blast
qed (fastforce)

(*------------------------------------------------------------------*)
subsubsection \<open>Injective\<close>

lemma helper_inj_head:
  assumes f_def: "f = fun_upd_list f0 (zip xs ys)"
      and distinct_ys: "distinct ys"
      and length_equal: "length xs = length ys"
      and non_empty: "xs \<noteq> []"
      and 0: "a \<in> set xs \<and> b \<in> set xs \<and> a \<noteq> b"
      and 1: "a = hd xs \<and> b \<in> set (tl xs)"
    shows "f a \<noteq> f b"
  using assms
  by (metis distinct.simps(2) fun_upd_list_hd_1 fun_upd_list_not_hd helper_surj_zip_1 length_0_conv 
            length_tl list.collapse)

lemma helper_inj_tail:
  assumes "distinct xs"
      and "distinct ys"
      and "length xs = length ys"
      and "a \<in> set (tl xs)"
      and "b \<in> set (tl xs)"
      and "a \<noteq> b"
    shows "fun_upd_list f (zip xs ys) a \<noteq> fun_upd_list f (zip xs ys) b"
using assms proof (induct xs arbitrary: ys)
  case (Cons x xs)

  have a_elem: "a \<in> set (tl (x # xs))" using Cons.prems(4) by simp
  have b_elem: "b \<in> set (tl (x # xs))" using Cons.prems(5) by simp

  have a_not_hd: "a \<noteq> x" using Cons.prems(1) Cons.prems(4) by force
  have b_not_hd: "b \<noteq> x" using Cons.prems(1) Cons.prems(5) by force

  (* set-up complete, now the main part of the proof *)

  have a: "fun_upd_list f (zip (x # xs) ys) a = fun_upd_list f (zip xs (tl ys)) a"
    using a_not_hd fun_upd_list_not_hd
    by (metis Cons.prems(3) length_0_conv list.collapse list.distinct(1))
  
  have uneq: "fun_upd_list f (zip xs (tl ys)) a \<noteq> fun_upd_list f (zip xs (tl ys)) b"
    by (metis (no_types, lifting) a_elem b_elem helper_inj_head
        Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(3) Cons.prems(6)
        distinct_tl length_tl list.collapse list.sel(2) list.sel(3) set_ConsD)

  have b: "fun_upd_list f (zip xs (tl ys)) b = fun_upd_list f (zip (x # xs) ys) b"
    using b_not_hd fun_upd_list_not_hd
    by (metis Cons.prems(3) length_0_conv list.collapse list.distinct(1))

  from a uneq b show ?case by simp
qed (simp)

theorem fun_upd_list_inj_zip:
  assumes "distinct xs"
      and "distinct ys"
      and "length xs = length ys"
      and "xs \<noteq> []"
    shows "inj_on (fun_upd_list f (zip xs ys)) (set xs)"
proof-
{ fix a b assume 0: "a \<in> set xs \<and> b \<in> set xs \<and> a \<noteq> b"
  hence "(a = hd xs \<and> b \<in> set (tl xs)) \<or>
        (b = hd xs \<and> a \<in> set (tl xs)) \<or>
        (a \<in> set (tl xs) \<and> b \<in> set (tl xs))"
    using assms(4) by (metis list.collapse set_ConsD)
  moreover
  { assume "a = hd xs \<and> b \<in> set (tl xs)"
    hence "(fun_upd_list f (zip xs ys)) a \<noteq> (fun_upd_list f (zip xs ys)) b"
      using 0 assms helper_inj_head by metis }
  moreover
  { assume "b = hd xs \<and> a \<in> set (tl xs)"
    hence "(fun_upd_list f (zip xs ys)) a \<noteq> (fun_upd_list f (zip xs ys)) b"
      using 0 assms helper_inj_head by metis }
  moreover
  { assume "a \<in> set (tl xs) \<and> b \<in> set (tl xs)"
    hence "fun_upd_list f (zip xs ys) a \<noteq> fun_upd_list f (zip xs ys) b"
      using helper_inj_tail by (metis 0 assms(1) assms(2) assms(3)) }
  ultimately have "(fun_upd_list f (zip xs ys)) a \<noteq> (fun_upd_list f (zip xs ys)) b"
    by force }
  thus ?thesis by (meson inj_onI)
qed

theorem fun_upd_list_surj_zip:
  assumes "f = fun_upd_list f0 (zip xs ys)"
      and "distinct xs"
      and "length xs = length ys"
    shows "f ` set xs = set ys"
  by (metis assms fun_upd_list_surj_map_2 fun_upd_list_surj_zip_1
            inf.absorb_iff2 inf.order_iff zip_eq_conv)

theorem fun_upd_list_bij_betw_zip:
  assumes "distinct xs"
      and "distinct ys"
      and "length xs = length ys"
      and "xs \<noteq> []"
    shows "bij_betw (fun_upd_list f (zip xs ys)) (set xs) (set ys)"
  using assms
  by (fastforce simp add: bij_betw_def fun_upd_list_inj_zip fun_upd_list_surj_zip)

lemma fun_upd_list_distinct:
  assumes "distinct (map snd (xy # xys))"
      and "f x \<notin> set (map snd (xy # xys))"
    shows "fun_upd_list f xys x \<noteq> snd xy"
  by (metis assms fun_upd_list_not_updated_map fun_upd_list_surj_map_1
            distinct.simps(2) image_eqI list.set_intros(1) list.simps(9) subsetD)

theorem inj_img_fun_upd_list_map:
  assumes "distinct (map snd xys)"
      and "\<forall> x. f x \<notin> set (map snd xys)"
    shows "inj_img (fun_upd_list f xys) (set (map snd xys))"
using assms proof (induct xys)
  case (Cons xy xys)
  hence"inj_img (fun_upd_list f xys) ({snd xy} \<union> set (map snd xys))"
    by (fastforce simp: fun_upd_list_distinct inj_img_def)
  thus ?case
    unfolding inj_img_def apply clarsimp
    by (metis Cons.prems(1,2) fun_upd_list_distinct)
qed (fastforce simp: inj_img_not_mapped_to)

theorem inj_img_fun_upd_list_zip:
  assumes "distinct ys"
      and "length xs = length ys"
      and "\<forall> x. f x \<notin> set ys"
    shows "inj_img (fun_upd_list f (zip xs ys)) (set ys)"
  by (metis assms inj_img_fun_upd_list_map map_snd_zip)

(*----------------------------------------------------------------------------*)
subsubsection \<open>Set- and List-Intervals\<close>

lemma fun_upd_list_new_interval:
  assumes "length xs = length ys"
  shows "fun_upd_list f (zip xs ys) i \<in> {f i} \<union> set ys"
  apply (cases "i \<in> set xs")
   apply (fastforce simp: assms intro: helper_surj_zip_1)
  by (fastforce intro: fun_upd_list_not_updated_zip)


lemma helper_interval_length:
  "length [1 ..< length xs + 1] = length xs"
  apply (subst length_upt)
  by fastforce 

lemma helper_interval_union:
  "{0::nat} \<union> {1 ..< n + 1} = {0 ..< n + 1}"
  by force

lemma fun_upd_list_interval:
  "fun_upd_list (\<lambda>x.0) (zip xs [1 ..< length xs + 1]) z \<in> {0 ..< length xs + 1}"
  apply (cases "z \<in> set xs")
   apply (metis Un_iff set_upt helper_interval_union helper_interval_length helper_surj_zip_1)
  by (metis fun_upd_list_not_updated_zip add.commute atLeastLessThan_iff less_numeral_extra(1) 
            trans_less_add1 zero_le)

theorem fun_upd_list_interval_bij:
  assumes "f = fun_upd_list (\<lambda>x.0) (zip xs [1 ..< length xs + 1])"
      and "distinct xs"
    shows "bij_betw f {i. 1 \<le> f i} {1 ..< length xs + 1}"
proof-
  have set_xs : "set [1 ..< length xs + 1] = {1 ..< length xs + 1}" 
    by force
  have "set xs = {i. 1 \<le> f i}"
  proof (rule antisym)
    show "set xs \<subseteq> {i. 1 \<le> f i}"
      by (metis One_nat_def assms(1) atLeastLessThan_iff helper_interval_length helper_surj_zip_1 
                set_xs mem_Collect_eq subset_code(1))
    show "{i. 1 \<le> f i} \<subseteq> set xs"
        by (metis assms(1) fun_upd_list_not_updated_zip CollectD not_one_le_zero subsetI)  
  qed
  thus ?thesis
    by (metis (mono_tags, lifting) assms(1,2) fun_upd_list_bij_betw_zip helper_interval_length
        One_nat_def add.right_neutral add_Suc_right bij_betwI' distinct_upt
        empty_iff empty_set le_numeral_extra(4) list.size(3)
        set_xs upt_eq_Nil_conv)
qed

end
