theory Terms
  imports "Nominal-Utils" Vars  "AList-Utils-Nominal"
begin

subsubsection {* Expressions *}

text {*
This is the main data type of the development; our minimal lambda calculus with recursive let-bindings.
It is created using the nominal\_datatype command, which creates alpha-equivalence classes.

The package does not support nested recursion, so the bindings of the let cannot simply be of type
@{text "(var, exp) list"}. Instead, the definition of lists have to be inlined here, as the custom type
@{text "assn"}. Later we create conversion functions between these two types, define a properly typed @{text let} 
and redo the various lemmas in terms of that, so that afterwards, the type @{text "assn"} is no longer
referenced.
*}

nominal_datatype exp =
  Var "var"
| App "exp" "var"
| LetA as::"assn" body::"exp" binds "bn as" in "body" "as"
| Lam x::"var" body::"exp" binds x in body  ("Lam [_]. _" [100, 100] 100)
and assn =
  ANil | ACons "var" "exp" "assn" 
binder
  bn
where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

notation (latex output) Terms.Var ("_")
notation (latex output) Terms.App ("_ _")
notation (latex output) Terms.Lam ("\<lambda>_. _"  [100, 100] 100)

type_synonym heap = "(var \<times> exp) list"

subsubsection {* Rewriting in terms of heaps *}

text {*
We now work towards using @{type heap} instead of @{type assn}. All this
could be skipped if Nominal supported nested recursion.
*}

text {*
Conversion from @{typ assn} to @{typ heap}.
*}

nominal_primrec asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # asToHeap as"
unfolding eqvt_def asToHeap_graph_aux_def
apply rule
apply simp
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
termination(eqvt) by lexicographic_order

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

text {* The other direction. *}

fun heapToAssn :: "heap \<Rightarrow> assn"
  where "heapToAssn [] = ANil" 
  | "heapToAssn ((v,e)#\<Gamma>) = ACons v e (heapToAssn \<Gamma>)"
declare heapToAssn.simps[simp del]

lemma heapToAssn_eqvt[simp,eqvt]: "p \<bullet> heapToAssn \<Gamma> =  heapToAssn (p \<bullet> \<Gamma>)"
  by (induct \<Gamma> rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma bn_heapToAssn: "bn (heapToAssn \<Gamma>) = map (\<lambda>x. atom (fst x)) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps exp_assn.bn_defs)

lemma set_bn_to_atom_domA:
  "set (bn as) = atom ` domA (asToHeap as)"
   by (induct as rule: asToHeap.induct)
      (auto simp add: exp_assn.bn_defs)

text {*
They are inverse to each other.
*}

lemma heapToAssn_asToHeap[simp]:
  "heapToAssn (asToHeap as) = as"
  by (induct  rule: exp_assn.inducts(2)[of "\<lambda> _ . True"])
     (auto simp add: heapToAssn.simps)

lemma asToHeap_heapToAssn[simp]:
  "asToHeap (heapToAssn as) = as"
  by (induct rule: heapToAssn.induct)
     (auto simp add: heapToAssn.simps)

lemma heapToAssn_inject[simp]:
  "heapToAssn x = heapToAssn y \<longleftrightarrow> x = y"
  by (metis asToHeap_heapToAssn)

text {*
They are transparent to varios notions from the Nominal package.
*}

lemma supp_heapToAssn: "supp (heapToAssn \<Gamma>) = supp \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma supp_asToHeap: "supp (asToHeap as) = supp as"
   by (induct as rule: asToHeap.induct)
      (simp_all add:  exp_assn.supp supp_Nil supp_Cons supp_Pair sup_assoc)

lemma fv_asToHeap: "fv (asToHeap \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_asToHeap)

lemma fv_heapToAssn: "fv (heapToAssn \<Gamma>) = fv \<Gamma>"
  unfolding fv_def by (auto simp add: supp_heapToAssn)

lemma [simp]: "size (heapToAssn \<Gamma>) = list_size (\<lambda> (v,e) . size e) \<Gamma>"
  by (induct rule: heapToAssn.induct)
     (simp_all add: heapToAssn.simps)

text {* Now we define the Let constructor in the form that we actually want. *}

hide_const HOL.Let
definition Let :: "heap \<Rightarrow> exp \<Rightarrow> exp"
  where "Let \<Gamma> e = LetA (heapToAssn \<Gamma>) e"

notation (latex output) Let ("\<^raw:\textrm{\textsf{let}}> _ \<^raw:\textrm{\textsf{in}}> _")

abbreviation
  LetBe :: "var\<Rightarrow>exp\<Rightarrow>exp\<Rightarrow>exp" ("let _ be _ in _ " [100,100,100] 100)
where
  "let x be t1 in t2 \<equiv> Let [(x,t1)] t2"

text {*
We rewrite all (relevant) lemmas about @{term LetA} in terms of @{term Let}.
*}

lemma size_Let[simp]: "size (Let \<Gamma> e) = list_size (\<lambda>p. size (snd p)) \<Gamma> + size e + Suc 0"
  unfolding Let_def by (auto simp add: split_beta')

lemma Let_distinct[simp]:
  "Var v \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Var v"
  "App e v \<noteq> Let \<Gamma> e'"
  "Lam [v]. e' \<noteq> Let \<Gamma> e"
  "Let \<Gamma> e \<noteq> Lam [v]. e'"
  "Let \<Gamma> e' \<noteq> App e v"
  unfolding Let_def by simp_all

lemma Let_perm_simps[simp,eqvt]:
  "p \<bullet> Let \<Gamma> e = Let (p \<bullet> \<Gamma>) (p \<bullet> e)"
  unfolding Let_def by simp

lemma Let_supp:
  "supp (Let \<Gamma> e) = (supp e \<union> supp \<Gamma>) - atom ` (domA \<Gamma>)"
  unfolding Let_def by (simp add: exp_assn.supp supp_heapToAssn bn_heapToAssn domA_def image_image)

lemma Let_fresh[simp]:
  "a \<sharp> Let \<Gamma> e = (a \<sharp> e \<and> a \<sharp> \<Gamma> \<or> a \<in> atom ` domA \<Gamma>)"
  unfolding fresh_def by (auto simp add: Let_supp)

lemma Abs_eq_cong:
  assumes "\<And> p. (p \<bullet> x = x') \<longleftrightarrow> (p \<bullet> y = y')"
  assumes "supp y = supp x"
  assumes "supp y' = supp x'"
  shows "([a]lst. x = [a']lst. x') \<longleftrightarrow> ([a]lst. y = [a']lst. y')"
  by (simp add: Abs_eq_iff alpha_lst assms)

lemma Let_eq_iff[simp]:
  "(Let \<Gamma> e = Let \<Gamma>' e') = ([map (\<lambda>x. atom (fst x)) \<Gamma> ]lst. (e, \<Gamma>) = [map (\<lambda>x. atom (fst x)) \<Gamma>']lst. (e',\<Gamma>'))"
  unfolding Let_def 
  apply (simp add: bn_heapToAssn)
  apply (rule Abs_eq_cong)
  apply (simp_all add: supp_Pair supp_heapToAssn)
  done

lemma exp_strong_exhaust:
  fixes c :: "'a :: fs"
  assumes "(\<And>var. y = Var var \<Longrightarrow> P)"
  assumes "\<And>exp var. y = App exp var \<Longrightarrow> P"
  assumes "\<And>\<Gamma> exp. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> y = Let \<Gamma> exp \<Longrightarrow> P"
  assumes "\<And>var exp. {atom var} \<sharp>* c \<Longrightarrow> y = Lam [var]. exp \<Longrightarrow> P"
  shows P
  apply (rule  exp_assn.strong_exhaust(1)[where y = y and c = c])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap)
  apply (metis assms(4))
  done

text {*
And finally the induction rules with @{term Let}.
*}

lemma exp_heap_induct[case_names Var App Let Lam Nil Cons]:
  assumes "\<And>var. P1 (Var var)"
  assumes "\<And>exp var. P1 exp \<Longrightarrow> P1 (App exp var)"
  assumes "\<And>\<Gamma> exp. P2 \<Gamma> \<Longrightarrow> P1 exp \<Longrightarrow> P1 (Let \<Gamma> exp)"
  assumes "\<And>var exp. P1 exp \<Longrightarrow> P1 (Lam [var]. exp)"
  assumes "P2 []"
  assumes "\<And>var exp \<Gamma>. P1 exp \<Longrightarrow> P2 \<Gamma> \<Longrightarrow> P2 ((var, exp)#\<Gamma>)"
  shows "P1 e" and "P2 \<Gamma>"
proof-
  have "P1 e" and "P2 (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.inducts[of P1 "\<lambda> assn. P2 (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5) asToHeap.simps(1))
    apply (metis assms(6) asToHeap.simps(2))
    done
  thus "P1 e" and "P2 \<Gamma>" unfolding asToHeap_heapToAssn.
qed

lemma exp_heap_strong_induct[case_names Var App Let Lam Nil Cons]:
  assumes "\<And>var c. P1 c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P1 c exp) \<Longrightarrow> P1 c (App exp var)"
  assumes "\<And>\<Gamma> exp c. atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P1 c exp) \<Longrightarrow> P1 c (Lam [var]. exp)"
  assumes "\<And>c. P2 c []"
  assumes "\<And>var exp \<Gamma> c. (\<And>c. P1 c exp) \<Longrightarrow> (\<And>c. P2 c \<Gamma>) \<Longrightarrow> P2 c ((var,exp)#\<Gamma>)"
  fixes c :: "'a :: fs"
  shows "P1 c e" and "P2 c \<Gamma>"
proof-
  have "P1 c e" and "P2 c (asToHeap (heapToAssn \<Gamma>))"
    apply (induct rule: exp_assn.strong_induct[of P1 "\<lambda> c assn. P2 c (asToHeap assn)"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply (metis assms(3) set_bn_to_atom_domA Let_def heapToAssn_asToHeap )
    apply (metis assms(4))
    apply (metis assms(5) asToHeap.simps(1))
    apply (metis assms(6) asToHeap.simps(2))
    done
  thus "P1 c e" and "P2 c \<Gamma>" unfolding asToHeap_heapToAssn.
qed

subsubsection {* Nice induction rules *}

text {*
These rules can be used instead of the original induction rules, which require a separate
goal for @{typ assn}.
*}

lemma exp_induct[case_names Var App Let Lam]:
  assumes "\<And>var. P (Var var)"
  assumes "\<And>exp var. P exp \<Longrightarrow> P (App exp var)"
  assumes "\<And>\<Gamma> exp. (\<And> x. x \<in> domA \<Gamma> \<Longrightarrow>  P (the (map_of \<Gamma> x))) \<Longrightarrow> P exp \<Longrightarrow> P (Let \<Gamma> exp)"
  assumes "\<And>var exp.  P exp \<Longrightarrow> P (Lam [var]. exp)"
  shows "P  exp"
  apply (rule exp_heap_induct[of P "\<lambda> \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

lemma  exp_strong_induct[case_names Var App Let Lam]:
  assumes "\<And>var c. P c (Var var)"
  assumes "\<And>exp var c. (\<And>c. P c exp) \<Longrightarrow> P c (App exp var)"
  assumes "\<And>\<Gamma> exp c.
    atom ` domA \<Gamma> \<sharp>* c \<Longrightarrow> (\<And>c x. x \<in> domA \<Gamma> \<Longrightarrow>  P c (the (map_of \<Gamma> x))) \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Let \<Gamma> exp)"
  assumes "\<And>var exp c. {atom var} \<sharp>* c \<Longrightarrow> (\<And>c. P c exp) \<Longrightarrow> P c (Lam [var]. exp)"
  shows "P (c::'a::fs) exp"
  apply (rule exp_heap_strong_induct(1)[of P "\<lambda> c \<Gamma>. (\<forall>x \<in> domA \<Gamma>. P c (the (map_of \<Gamma> x)))"])
  apply (metis assms(1))
  apply (metis assms(2))
  apply (metis assms(3))
  apply (metis assms(4))
  apply auto
  done

subsubsection {* Testing alpha equivalence *}
              
lemma alpha_test:
  shows "Lam [x]. (Var x) = Lam [y]. (Var y)"
  by (simp add: Abs1_eq_iff fresh_at_base)

lemma alpha_test2:
  shows "let x be (Var x) in (Var x) = let y be (Var y) in (Var y)"
  by (simp add: fresh_Cons fresh_Nil Abs1_eq_iff fresh_Pair add: fresh_at_base)

lemma alpha_test3:
  shows "
    Let [(x, Var y), (y, Var x)] (Var x)
    =
    Let [(y, Var x), (x, Var y)] (Var y)" (is "Let ?la ?lb = _")
  by (simp add: bn_heapToAssn Abs1_eq_iff fresh_Pair fresh_at_base
                Abs_swap2[of "atom x" "(?lb, [(x, Var y), (y, Var x)])" "[atom x, atom y]" "atom y"])

subsubsection {* Free variables *}

lemma fv_supp_exp: "supp e = atom ` (fv (e::exp) :: var set)" and fv_supp_as: "supp as = atom ` (fv (as::assn) :: var set)"
  by (induction e and as rule:exp_assn.inducts)
     (auto simp add: fv_def exp_assn.supp supp_at_base)

lemma fv_supp_heap: "supp (\<Gamma>::heap) = atom ` (fv \<Gamma> :: var set)"
  by (metis fv_def fv_supp_as supp_heapToAssn)

lemma fv_Lam[simp]: "fv (Lam [x]. e) = fv e - {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp)
lemma fv_Var[simp]: "fv (Var x) = {x}"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_App[simp]: "fv (App e x) = insert x (fv e)"
  unfolding fv_def by (auto simp add: exp_assn.supp supp_at_base)
lemma fv_Let[simp]: "fv (Let \<Gamma> e) = (fv \<Gamma> \<union> fv e) - domA \<Gamma>"
  unfolding fv_def by (auto simp add: Let_supp exp_assn.supp supp_at_base set_bn_to_atom_domA)

lemma finite_fv_exp[simp]: "finite (fv (e::exp) :: var set)"
  and finite_fv_heap[simp]: "finite (fv (\<Gamma> :: heap) :: var set)"
  by (induction e rule:exp_heap_induct) auto

lemma fv_not_fresh: "atom x \<sharp> e \<longleftrightarrow> x \<notin> fv e"
  unfolding fv_def fresh_def by blast

lemma fv_delete_heap:
  assumes "map_of \<Gamma> x = Some e"
  shows "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> (fv (\<Gamma>, Var x) :: var set)"
proof-
  have "fv (delete x \<Gamma>) \<subseteq> fv \<Gamma>" by (metis fv_delete_subset)
  moreover
  have "(x,e) \<in> set \<Gamma>" by (metis assms map_of_is_SomeD)
  hence "fv e \<subseteq> fv \<Gamma>" by (metis assms domA_from_set map_of_fv_subset the.simps)
  moreover
  have "x \<in> fv (Var x)" by simp
  ultimately show ?thesis by auto
qed

end
