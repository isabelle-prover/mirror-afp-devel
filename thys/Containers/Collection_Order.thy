(* Title:      Containers/Collection_Order.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Collection_Order
imports
  Set_Linorder
  Containers_Generator
  "../Datatype_Order_Generator/Order_Generator"
begin

chapter {* Light-weight containers *}
text_raw {* \label{chapter:light-weight:containers} *}

section {* A linear order for code generation *}

subsection {* Optional linear orders *}

class corder = 
  fixes corder :: "(('a \<Rightarrow> 'a \<Rightarrow> bool) * ('a \<Rightarrow> 'a \<Rightarrow> bool)) option"
  assumes corder: "\<And>less_eq less. corder = Some (less_eq, less) \<Longrightarrow> class.linorder less_eq less"
begin

lemma ID_corder: "\<And>less_eq less. ID corder = Some (less_eq, less) \<Longrightarrow> class.linorder less_eq less"
unfolding ID_def id_apply by(rule corder)

abbreviation cless_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "cless_eq \<equiv> fst (the (ID corder))"
abbreviation cless :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "cless \<equiv> snd (the (ID corder))"

end

syntax "_CORDER" :: "type => logic" ("(1CORDER/(1'(_')))")

parse_translation {*
let
  fun corder_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "corder"} $
       (Syntax.const @{type_syntax option} $
         (Syntax.const @{type_syntax prod} $
           (Syntax.const @{type_syntax fun} $ ty $
             (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax bool})) $
           (Syntax.const @{type_syntax fun} $ ty $
             (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax bool})))))
    | corder_tr ts = raise TERM ("corder_tr", ts);
in [(@{syntax_const "_CORDER"}, K corder_tr)] end
*}

typed_print_translation {*
let
  fun corder_tr' ctxt
    (Type (@{type_name option}, [Type (@{type_name prod}, [Type (@{type_name fun}, [T, _]), _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_CORDER"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | corder_tr' _ _ _ = raise Match;
in [(@{const_syntax corder}, corder_tr')]
end
*}

context corder begin

lemma cless_eq_conv_cless: 
  fixes a b :: "'a"
  assumes "ID CORDER('a) \<noteq> None"
  shows "cless_eq a b \<longleftrightarrow> cless a b \<or> a = b"
proof -
  from assms interpret linorder cless_eq "cless :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
    by(clarsimp simp add: ID_corder)
  show ?thesis by(rule le_less)
qed

end

definition is_corder :: "'a :: corder itself \<Rightarrow> bool"
where "is_corder _ \<longleftrightarrow> ID CORDER('a) \<noteq> None"

subsection {* Generator for the @{class corder}-class *}

text {*
This generator registers itself at the derive-manager for the class
@{class corder}. To be more precise, one can choose whether one does not want to
support a linear order by passing parameter "no", one wants to register an arbitrary type which
is already in class @{class linorder} using parameter "linorder", or
one wants to generate a new linear order by passing no parameter.
In the last case, one demands that the type is a datatype
and that all non-recursive types of that datatype are in class @{class linorder}. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (no) corder}
\item \texttt{instantiation type :: (linorder,\ldots,linorder) corder}
\item \texttt{instantiation datatype :: (linorder,\ldots,linorder) (linorder) corder}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{term is_corder}-theorem is automatically generated and attributed with 
\texttt{[simp, code-post]}.
*}


text {* 
To create a new ordering, we just invoke the functionality provided by the order generator.
The only difference is the boilerplate-code, which for the order generator has to perform
the class instantiation for an order, whereas here we have to invoke the methods to 
satisfy the corresponding locale for linear orders.
*}

text {*
This generator can be used for arbitrary types, not just datatypes. 
When passing no parameters, we get same limitation as for the order generator.
For mutual recursive datatypes, only for the first mentioned datatype the instantiations 
of the @{class corder} classes are derived.
*}

lemma corder_intro: "class.linorder le lt \<Longrightarrow> a = Some (le, lt)\<Longrightarrow> a = Some (le',lt') \<Longrightarrow>
  class.linorder le' lt'" by auto

ML_file "corder_generator.ML"

subsection {* Instantiations for HOL types *}

derive (linorder) corder unit
derive (linorder) corder bool
derive (linorder) corder nat
derive (linorder) corder int
derive (linorder) corder Enum.finite_1
derive (linorder) corder Enum.finite_2 
derive (linorder) corder Enum.finite_3
derive (no) corder Enum.finite_4
derive (no) corder Enum.finite_5

derive (linorder) corder integer
derive (linorder) corder natural
derive (linorder) corder nibble
derive (linorder) corder char
derive (linorder) corder String.literal

instantiation sum :: (corder, corder) corder begin
definition "CORDER('a + 'b) = 
  (case ID CORDER('a) of None \<Rightarrow> None
   | Some (leq_a, lt_a) \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> None
     | Some (leq_b, lt_b) \<Rightarrow> 
       Some
         (\<lambda>x y. case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> leq_a xl yl | _ \<Rightarrow> True)
                | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> leq_b xr yr | _ \<Rightarrow> False),
          \<lambda>x y. case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> lt_a xl yl | _ \<Rightarrow> True)
                | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> lt_b xr yr | _ \<Rightarrow> False)))"
instance
proof(intro_classes)
  fix leq lt
  assume "CORDER('a + 'b) = Some (leq, lt)"
  then obtain leq_a lt_a leq_b lt_b 
    where a: "ID CORDER('a) = Some (leq_a, lt_a)" 
    and b: "ID CORDER('b) = Some (leq_b, lt_b)"
    and leq: "\<And>x y. leq x y = (case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> leq_a xl yl | _ \<Rightarrow> True)
                               | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> leq_b xr yr | _ \<Rightarrow> False))"
    and lt: "\<And>x y. lt x y = (case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> lt_a xl yl | _ \<Rightarrow> True)
                             | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> lt_b xr yr | _ \<Rightarrow> False))"
    by(fastforce simp add: corder_sum_def split: option.split_asm)
  from a interpret a!: linorder leq_a lt_a by(rule ID_corder)
  from b interpret b!: linorder leq_b lt_b by(rule ID_corder)
  show "class.linorder leq lt"
    by(unfold_locales)(auto simp add: lt leq split: sum.splits)
qed
end

lemma is_corder_sum [simp, code_post]:
  "is_corder TYPE('a + 'b) \<longleftrightarrow> is_corder TYPE('a :: corder) \<and> is_corder TYPE('b :: corder)"
by(simp add: is_corder_def corder_sum_def ID_None ID_Some split: option.split)

instantiation prod :: (corder, corder) corder begin
definition "CORDER('a * 'b) =
  (case ID CORDER('a) of None \<Rightarrow> None
   | Some (leq_a, lt_a) \<Rightarrow>
     case ID CORDER('b) of None \<Rightarrow> None
     | Some (leq_b, lt_b) \<Rightarrow>
       Some (less_eq_prod leq_a lt_a leq_b, less_prod leq_a lt_a lt_b))"
instance
proof
  fix leq lt
  assume "CORDER('a * 'b) = Some (leq, lt)"
  then obtain leq_a lt_a leq_b lt_b 
    where a: "ID CORDER('a) = Some (leq_a, lt_a)" 
    and b: "ID CORDER('b) = Some (leq_b, lt_b)"
    and leq: "leq = less_eq_prod leq_a lt_a leq_b"
    and lt: "lt = less_prod leq_a lt_a lt_b"
    by(auto simp add: corder_prod_def split: option.split_asm prod.split_asm)
  from a b have "class.linorder leq_a lt_a" "class.linorder leq_b lt_b"
    by(blast intro: ID_corder)+
  thus "class.linorder leq lt" unfolding leq lt by(rule linorder_prod)
qed
end

lemma is_corder_prod [simp, code_post]:
  "is_corder TYPE('a \<times> 'b) \<longleftrightarrow> is_corder TYPE('a :: corder) \<and> is_corder TYPE('b :: corder)"
by(simp add: is_corder_def corder_prod_def ID_None ID_Some split: option.split)

instantiation list :: (corder) corder begin
definition "CORDER('a list) =
  map_option (\<lambda>(leq, lt). (\<lambda>xs ys. ord.lexordp_eq lt xs ys, ord.lexordp lt)) (ID CORDER('a))"
instance
proof
  fix leq lt
  assume "CORDER('a list) = Some (leq, lt)"
  then obtain leq_a lt_a where a: "ID CORDER('a) = Some (leq_a, lt_a)"
    and leq: "\<And>xs ys. leq xs ys \<longleftrightarrow> ord.lexordp_eq lt_a xs ys"
    and lt: "\<And>xs ys. lt xs ys \<longleftrightarrow> ord.lexordp lt_a xs ys"
    by(auto simp add: corder_list_def)
  from a interpret a!: linorder leq_a lt_a by(rule ID_corder)
  show "class.linorder leq lt" unfolding leq[abs_def] lt[abs_def]
    by(rule a.lexordp_linorder)
qed
end

lemma is_corder_list [simp, code_post]:
  "is_corder TYPE('a list) \<longleftrightarrow> is_corder TYPE('a :: corder)"
by(simp add: is_corder_def corder_list_def ID_def)

instantiation option :: (corder) corder begin
definition "CORDER('a option) =
  map_option (\<lambda>(leq, lt). (\<lambda>x y. case x of None \<Rightarrow> True | Some x' \<Rightarrow> case y of None \<Rightarrow> False | Some y' \<Rightarrow> leq x' y',
                           \<lambda>x y. case y of None \<Rightarrow> False | Some y' \<Rightarrow> case x of None \<Rightarrow> True | Some x' \<Rightarrow> lt x' y')) 
    (ID CORDER('a))"
instance
proof
  fix leq lt
  assume "CORDER('a option) = Some (leq, lt)"
  then obtain leq_a lt_a where a: "ID CORDER('a) = Some (leq_a, lt_a)"
    and leq: "\<And>x y. leq x y \<longleftrightarrow> (case x of None \<Rightarrow> True | Some x' \<Rightarrow> case y of None \<Rightarrow> False | Some y' \<Rightarrow> leq_a x' y')"
    and lt: "\<And>x y. lt x y \<longleftrightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> case x of None \<Rightarrow> True | Some x' \<Rightarrow> lt_a x' y')"
    by(auto simp add: corder_option_def)
  from a interpret a!: linorder leq_a lt_a by(rule ID_corder)
  show "class.linorder leq lt" by(unfold_locales)(auto simp add: leq lt split: option.splits)
qed
end

lemma is_corder_option [simp, code_post]:
  "is_corder TYPE('a option) \<longleftrightarrow> is_corder TYPE('a :: corder)"
by(simp add: is_corder_def corder_option_def ID_def)

derive (no) corder "fun"

lemma is_corder_fun [simp]: "\<not> is_corder TYPE('a \<Rightarrow> 'b)"
by(simp add: is_corder_def corder_fun_def ID_None)

instantiation set :: (corder) corder begin
definition "CORDER('a set) = map_option (\<lambda>(leq, lt). (ord.set_less_eq leq, ord.set_less leq)) (ID CORDER('a))"
instance by(intro_classes)(auto simp add: corder_set_def intro: linorder.set_less_eq_linorder ID_corder)
end

lemma is_corder_set [simp, code_post]:
  "is_corder TYPE('a set) \<longleftrightarrow> is_corder TYPE('a :: corder)"
by(simp add: is_corder_def corder_set_def ID_def)


definition cless_eq_set :: "'a :: corder set \<Rightarrow> 'a set \<Rightarrow> bool" 
where [simp, code del]: "cless_eq_set = fst (the (ID CORDER('a set)))"

definition cless_set :: "'a :: corder set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del]: "cless_set = snd (the (ID CORDER('a set)))"

lemma corder_set_code [code]:
  "CORDER('a :: corder set) = (case ID CORDER('a) of None \<Rightarrow> None | Some _ \<Rightarrow> Some (cless_eq_set, cless_set))"
by(clarsimp simp add: corder_set_def ID_Some split: option.split)

derive (no) corder Predicate.pred

subsection {* Proper intervals *}

class cproper_interval = corder + 
  fixes cproper_interval :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  assumes cproper_interval: 
  "\<lbrakk> ID CORDER('a) \<noteq> None; finite (UNIV :: 'a set) \<rbrakk>
  \<Longrightarrow> class.proper_interval cless cproper_interval"
begin

lemma ID_corder_interval: 
  "\<lbrakk> ID CORDER('a) = Some (leq, lt); finite (UNIV :: 'a set) \<rbrakk>
  \<Longrightarrow> class.linorder_proper_interval leq lt cproper_interval"
using cproper_interval
by(simp add: ID_corder class.linorder_proper_interval_def)

end

instantiation unit :: cproper_interval begin
definition "cproper_interval = (proper_interval :: unit proper_interval)"
instance by(intro_classes)(simp add: cproper_interval_unit_def corder_unit_def ID_Some proper_interval_class.axioms)
end

instantiation bool :: cproper_interval begin
definition "cproper_interval = (proper_interval :: bool proper_interval)"
instance by(intro_classes)(simp add: cproper_interval_bool_def corder_bool_def ID_Some proper_interval_class.axioms)
end

instantiation nat :: cproper_interval begin
definition "cproper_interval = (proper_interval :: nat proper_interval)"
instance by intro_classes simp
end

instantiation int :: cproper_interval begin
definition "cproper_interval = (proper_interval :: int proper_interval)"
instance by intro_classes (simp add: cproper_interval_int_def corder_int_def ID_Some proper_interval_class.axioms)
end

instantiation integer :: cproper_interval begin
definition "cproper_interval = (proper_interval :: integer proper_interval)"
instance by intro_classes (simp add: cproper_interval_integer_def corder_integer_def ID_Some proper_interval_class.axioms)
end

instantiation natural :: cproper_interval begin
definition "cproper_interval = (proper_interval :: natural proper_interval)"
instance by intro_classes (simp add: cproper_interval_natural_def corder_natural_def ID_Some proper_interval_class.axioms)
end

instantiation nibble :: cproper_interval begin
definition "cproper_interval = (proper_interval :: nibble proper_interval)"
instance by intro_classes (simp add: cproper_interval_nibble_def corder_nibble_def ID_Some proper_interval_class.axioms)
end

instantiation char :: cproper_interval begin
definition "cproper_interval = (proper_interval :: char proper_interval)"
instance by intro_classes (simp add: cproper_interval_char_def corder_char_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_1 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_1 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_1_def corder_finite_1_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_2 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_2 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_2_def corder_finite_2_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_3 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: Enum.finite_3 proper_interval)"
instance by intro_classes (simp add: cproper_interval_finite_3_def corder_finite_3_def ID_Some proper_interval_class.axioms)
end

instantiation Enum.finite_4 :: cproper_interval begin
definition "(cproper_interval :: Enum.finite_4 proper_interval) _ _ = undefined"
instance by intro_classes(simp add: corder_finite_4_def ID_None)
end

instantiation Enum.finite_5 :: cproper_interval begin
definition "(cproper_interval :: Enum.finite_5 proper_interval) _ _ = undefined"
instance by intro_classes(simp add: corder_finite_5_def ID_None)
end

instantiation sum :: (cproper_interval, cproper_interval) cproper_interval begin
fun cproper_interval_sum :: "('a + 'b) proper_interval" where
  "cproper_interval_sum None None \<longleftrightarrow> True"
| "cproper_interval_sum None (Some (Inl x)) \<longleftrightarrow> cproper_interval None (Some x)"
| "cproper_interval_sum None (Some (Inr y)) \<longleftrightarrow> True"
| "cproper_interval_sum (Some (Inl x)) None \<longleftrightarrow> True"
| "cproper_interval_sum (Some (Inl x)) (Some (Inl y)) \<longleftrightarrow> cproper_interval (Some x) (Some y)"
| "cproper_interval_sum (Some (Inl x)) (Some (Inr y)) \<longleftrightarrow> cproper_interval (Some x) None \<or> cproper_interval None (Some y)"
| "cproper_interval_sum (Some (Inr y)) None \<longleftrightarrow> cproper_interval (Some y) None"
| "cproper_interval_sum (Some (Inr y)) (Some (Inl x)) \<longleftrightarrow> False"
| "cproper_interval_sum (Some (Inr x)) (Some (Inr y)) \<longleftrightarrow> cproper_interval (Some x) (Some y)"
instance
proof
  assume "ID CORDER('a + 'b) \<noteq> None" "finite (UNIV :: ('a + 'b) set)"
  then obtain leq_a lt_a leq_b lt_b 
    where A: "ID CORDER('a) = Some (leq_a, lt_a)" "finite (UNIV :: 'a set)"
    and B: "ID CORDER('b) = Some (leq_b, lt_b)" "finite (UNIV :: 'b set)" 
    by(fastforce simp add: corder_sum_def ID_Some ID_None split: option.split_asm)
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] corder_sum_def ID_Some
    and [split] = sum.split
  show "class.proper_interval cless (cproper_interval :: ('a + 'b) proper_interval)"
  proof
    fix y :: "'a + 'b"
    show "cproper_interval None (Some y) = (\<exists>z. cless z y)"
      using A B by(cases y)(auto, case_tac z, auto)

    fix x :: "'a + 'b"
    show "cproper_interval (Some x) None = (\<exists>z. cless x z)"
      using A B by(cases x)(auto, case_tac z, auto)

    show "cproper_interval (Some x) (Some y) = (\<exists>z. cless x z \<and> cless z y)"
      using A B by(cases x)(case_tac [!] y, auto, case_tac [!] z, auto)
  qed simp
qed
end

instantiation prod :: (cproper_interval, cproper_interval) cproper_interval begin
fun cproper_interval_prod :: "('a \<times> 'b) proper_interval" where
  "cproper_interval_prod None None \<longleftrightarrow> True"
| "cproper_interval_prod None (Some (y1, y2)) \<longleftrightarrow> cproper_interval None (Some y1) \<or> cproper_interval None (Some y2)"
| "cproper_interval_prod (Some (x1, x2)) None \<longleftrightarrow> cproper_interval (Some x1) None \<or> cproper_interval (Some x2) None"
| "cproper_interval_prod (Some (x1, x2)) (Some (y1, y2)) \<longleftrightarrow> 
   cproper_interval (Some x1) (Some y1) \<or> 
   cless x1 y1 \<and> (cproper_interval (Some x2) None \<or> cproper_interval None (Some y2)) \<or>
   \<not> cless y1 x1 \<and> cproper_interval (Some x2) (Some y2)"
instance
proof
  assume "ID CORDER('a \<times> 'b) \<noteq> None" "finite (UNIV :: ('a \<times> 'b) set)"
  then obtain leq_a lt_a leq_b lt_b 
    where A: "ID CORDER('a) = Some (leq_a, lt_a)" "finite (UNIV :: 'a set)"
    and B: "ID CORDER('b) = Some (leq_b, lt_b)" "finite (UNIV :: 'b set)"
    by(fastforce simp add: corder_prod_def ID_Some ID_None finite_prod split: option.split_asm)
  interpret a!: linorder leq_a lt_a by(rule ID_corder)(rule A) 
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] corder_prod_def ID_Some
    and [split] = sum.split
  show "class.proper_interval cless (cproper_interval :: ('a \<times> 'b) proper_interval)" using A B
    by unfold_locales (auto 4 4)
qed
end

instantiation list :: (corder) cproper_interval begin
definition cproper_interval_list :: "'a list proper_interval"
where "cproper_interval_list xso yso = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_listI)
end

lemma UNIV_literal_eq_range_STR: "UNIV = range STR"
by(auto intro: explode_inverse[symmetric])

lemma infinite_UNIV_literal: "\<not> finite (UNIV :: String.literal set)"
by(auto simp add: UNIV_literal_eq_range_STR infinite_UNIV_listI dest!: finite_imageD intro: inj_onI)

instantiation String.literal :: cproper_interval begin
definition cproper_interval_literal :: "String.literal proper_interval"
where "cproper_interval_literal xso yso = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_literal)
end

instantiation option :: (cproper_interval) cproper_interval begin
fun cproper_interval_option :: "'a option proper_interval" where
  "cproper_interval_option None None \<longleftrightarrow> True"
| "cproper_interval_option None (Some x) \<longleftrightarrow> x \<noteq> None"
| "cproper_interval_option (Some x) None \<longleftrightarrow> cproper_interval x None"
| "cproper_interval_option (Some x) (Some None) \<longleftrightarrow> False"
| "cproper_interval_option (Some x) (Some (Some y)) \<longleftrightarrow> cproper_interval x (Some y)"
instance
proof
  assume "ID CORDER('a option) \<noteq> None" "finite (UNIV :: 'a option set)"
  then obtain leq_a lt_a
    where A: "ID CORDER('a) = Some (leq_a, lt_a)" "finite (UNIV :: 'a set)"
    by(auto simp add: corder_option_def ID_def)
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] corder_option_def ID_Some
  show "class.proper_interval cless (cproper_interval :: 'a option proper_interval)" using A
  proof(unfold_locales)
    fix x y :: "'a option"
    show "cproper_interval (Some x) None = (\<exists>z. cless x z)" using A
      by(cases x)(auto split: option.split intro: exI[where x="Some undefined"])

    show "cproper_interval (Some x) (Some y) = (\<exists>z. cless x z \<and> cless z y)" using A
      by(cases x y rule: option.exhaust[case_product option.exhaust])(auto cong: option.case_cong split: option.split)
  qed(auto split: option.splits)
qed
end

instantiation set :: (cproper_interval) cproper_interval begin
fun cproper_interval_set :: "'a set proper_interval" where
  [code]: "cproper_interval_set None None \<longleftrightarrow> True"
| [code]: "cproper_interval_set None (Some B) \<longleftrightarrow> (B \<noteq> {})"
| [code]: "cproper_interval_set (Some A) None \<longleftrightarrow> (A \<noteq> UNIV)"
| cproper_interval_set_Some_Some [code del]: -- {* Refine for concrete implementations *}
  "cproper_interval_set (Some A) (Some B) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> (\<exists>C. cless A C \<and> cless C B)"
instance
proof
  assume "ID CORDER('a set) \<noteq> None" "finite (UNIV :: 'a set set)"
  then obtain leq_a lt_a
    where A: "ID CORDER('a) = Some (leq_a, lt_a)" "finite (UNIV :: 'a set)"
    by(auto simp add: corder_set_def ID_def Finite_Set.finite_set)
  interpret a!: linorder leq_a lt_a by(rule ID_corder)(rule A) 
  note [simp] = proper_interval.proper_interval_simps[OF cproper_interval] corder_set_def ID_Some
  show "class.proper_interval cless (cproper_interval :: 'a set proper_interval)" using A
    by unfold_locales auto
qed

lemma Complement_cproper_interval_set_Complement:
  fixes A B :: "'a set"
  assumes corder: "ID CORDER('a) \<noteq> None"
  shows "cproper_interval (Some (- A)) (Some (- B)) = cproper_interval (Some B) (Some A)"
using assms
by(clarsimp simp add: corder_set_def ID_Some)(metis double_complement linorder.Compl_set_less_Compl[OF ID_corder])

end

instantiation "fun" :: (type, type) cproper_interval begin
text {* No interval checks on functions needed because we have not defined an order on them. *}
definition "cproper_interval = (undefined :: ('a \<Rightarrow> 'b) proper_interval)"
instance by(intro_classes)(simp add: corder_fun_def ID_None)
end

end