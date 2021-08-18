(* Title:     MiniML/Type.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "MiniML-types and type substitutions"

theory Type
imports Maybe
begin

\<comment> \<open>type expressions\<close>
datatype "typ" = TVar nat | Fun "typ" "typ" (infixr "->" 70)

\<comment> \<open>type schemata\<close>
datatype type_scheme = FVar nat | BVar nat | SFun type_scheme type_scheme (infixr "=->" 70)

\<comment> \<open>embedding types into type schemata\<close>
fun mk_scheme :: "typ => type_scheme" where
  "mk_scheme (TVar n) = (FVar n)"
| "mk_scheme (t1 -> t2) = ((mk_scheme t1) =-> (mk_scheme t2))"

\<comment> \<open>type variable substitution\<close>
type_synonym subst = "nat => typ"

class type_struct =
  fixes free_tv :: "'a => nat set"
    \<comment> \<open>@{text "free_tv s"}: the type variables occurring freely in the type structure s\<close>
  fixes free_tv_ML :: "'a => nat list"
    \<comment> \<open>executable version of @{text free_tv}: Implementation with lists\<close>
  fixes bound_tv :: "'a => nat set"
    \<comment> \<open>@{text "bound_tv s"}: the type variables occurring bound in the type structure s\<close>
  fixes min_new_bound_tv :: "'a => nat"
    \<comment> \<open>minimal new free / bound variable\<close>
  fixes app_subst :: "subst => 'a => 'a" ("$")
    \<comment> \<open>extension of substitution to type structures\<close>

instantiation "typ" :: type_struct
begin

fun free_tv_typ where
  free_tv_TVar:    "free_tv (TVar m) = {m}"
| free_tv_Fun:     "free_tv (t1 -> t2) = (free_tv t1) Un (free_tv t2)"

fun app_subst_typ where
  app_subst_TVar: "$ S (TVar n) = S n" 
| app_subst_Fun:  "$ S (t1 -> t2) = ($ S t1) -> ($ S t2)" 

instance ..

end

instantiation type_scheme :: type_struct
begin

fun free_tv_type_scheme where
  "free_tv (FVar m) = {m}"
| "free_tv (BVar m) = {}"
| "free_tv (S1 =-> S2) = (free_tv S1) Un (free_tv S2)"

fun free_tv_ML_type_scheme where
  "free_tv_ML (FVar m) = [m]"
| "free_tv_ML (BVar m) = []"
| "free_tv_ML (S1 =-> S2) = (free_tv_ML S1) @ (free_tv_ML S2)"

fun bound_tv_type_scheme where
  "bound_tv (FVar m) = {}"
| "bound_tv (BVar m) = {m}"
| "bound_tv (S1 =-> S2) = (bound_tv S1) Un (bound_tv S2)"

fun min_new_bound_tv_type_scheme where
  "min_new_bound_tv (FVar n) = 0"
| "min_new_bound_tv (BVar n) = Suc n"
| "min_new_bound_tv (sch1 =-> sch2) = max (min_new_bound_tv sch1) (min_new_bound_tv sch2)"

fun app_subst_type_scheme where
  "$ S (FVar n) = mk_scheme (S n)"
| "$ S (BVar n) = (BVar n)"
| "$ S (sch1 =-> sch2) = ($ S sch1) =-> ($ S sch2)"

instance ..

end

instantiation list :: (type_struct) type_struct
begin

fun free_tv_list where
  "free_tv [] = {}"
| "free_tv (x#l) = (free_tv x) Un (free_tv l)"

fun free_tv_ML_list where
  "free_tv_ML [] = []"
| "free_tv_ML (x#l) = (free_tv_ML x) @ (free_tv_ML l)"

fun bound_tv_list where
  "bound_tv [] = {}"
| "bound_tv (x#l) = (bound_tv x) Un (bound_tv l)"

definition app_subst_list where
  app_subst_list: "$ S = map ($ S)"

instance ..

end

text  
\<open>\<open>new_tv s n\<close> computes whether n is a new type variable w.r.t. a type 
   structure s, i.e. whether n is greater than any type variable 
   occurring in the type structure\<close>
definition
  new_tv :: "[nat,'a::type_struct] => bool" where
  "new_tv n ts = (\<forall>m. m:(free_tv ts) \<longrightarrow> m<n)"

\<comment> \<open>identity\<close>
definition
  id_subst :: subst where
  "id_subst = (\<lambda>n. TVar n)"

\<comment> \<open>domain of a substitution\<close>
definition
  dom :: "subst => nat set" where
  "dom S = {n. S n \<noteq> TVar n}" 

\<comment> \<open>codomain of a substitution: the introduced variables\<close>
definition
  cod :: "subst => nat set" where
  "cod S = (UN m:dom S. (free_tv (S m)))"

class of_nat =
  fixes of_nat :: "nat \<Rightarrow> 'a"

instantiation nat :: of_nat
begin

definition
  "of_nat n = n"

instance ..

end

class typ_of =
  fixes typ_of :: "'a \<Rightarrow> typ"

instantiation "typ" :: typ_of
begin

definition
  "typ_of T = T"

instance ..

end

instantiation "fun" :: (of_nat, typ_of) type_struct
begin

definition free_tv_fun where
  "free_tv f = (let S = \<lambda>n. typ_of (f (of_nat n)) in (dom S) Un (cod S))"

instance ..

end

lemma free_tv_subst:
  "free_tv S = (dom S) Un (cod S)"
by (simp add: free_tv_fun_def of_nat_nat_def typ_of_typ_def )

\<comment> \<open>unification algorithm mgu\<close>
axiomatization mgu :: "typ \<Rightarrow> typ \<Rightarrow> subst option" where
  mgu_eq:   "mgu t1 t2 = Some U \<Longrightarrow> $U t1 = $U t2"
  and mgu_mg:   "[| (mgu t1 t2) = Some U; $S t1 = $S t2 |] ==> \<exists>R. S = $R \<circ> U"
  and mgu_Some: "$S t1 = $S t2 \<Longrightarrow> \<exists>U. mgu t1 t2 = Some U"
  and mgu_free: "mgu t1 t2 = Some U \<Longrightarrow> free_tv U \<subseteq> free_tv t1 \<union> free_tv t2"


lemma mk_scheme_Fun:
  "mk_scheme t = sch1 =-> sch2 \<Longrightarrow> (\<exists>t1 t2. sch1 = mk_scheme t1 \<and> sch2 = mk_scheme t2)"
proof (induction t)
  case TVar thus ?case by auto
next
  case Fun thus ?case by auto
qed

lemma mk_scheme_injective: "(mk_scheme t = mk_scheme t') \<Longrightarrow> t = t'"
proof (induction t arbitrary: t')
  case TVar thus ?case by(cases t') auto
next
  case Fun thus ?case by(cases t') auto
qed

lemma free_tv_mk_scheme[simp]: "free_tv (mk_scheme t) = free_tv t"
by (induction t) auto

lemma subst_mk_scheme[simp]: "$ S (mk_scheme t) = mk_scheme ($ S t)"
by (induction t) auto


\<comment> \<open>constructor laws for @{text app_subst}\<close>

lemma app_subst_Nil[simp]: 
  "$ S [] = []"
by (simp add: app_subst_list)

lemma app_subst_Cons[simp]: 
  "$ S (x#l) = ($ S x)#($ S l)"
by (simp add: app_subst_list)


\<comment> \<open>constructor laws for @{text new_tv}\<close>

lemma new_tv_TVar[simp]: 
  "new_tv n (TVar m) = (m<n)"
by (simp add: new_tv_def)

lemma new_tv_FVar[simp]: 
  "new_tv n (FVar m) = (m<n)"
by (simp add: new_tv_def)

lemma new_tv_BVar[simp]: 
  "new_tv n (BVar m) = True"
by (simp add: new_tv_def)

lemma new_tv_Fun[simp]: 
  "new_tv n (t1 -> t2) = (new_tv n t1 \<and> new_tv n t2)"
by (auto simp: new_tv_def)

lemma new_tv_Fun2[simp]: 
  "new_tv n (t1 =-> t2) = (new_tv n t1 \<and> new_tv n t2)"
by (auto simp: new_tv_def)

lemma new_tv_Nil[simp]: 
  "new_tv n []"
by (simp add: new_tv_def)

lemma new_tv_Cons[simp]: 
  "new_tv n (x#l) = (new_tv n x \<and> new_tv n l)"
by (auto simp: new_tv_def)

lemma new_tv_TVar_subst[simp]: "new_tv n TVar"
by (simp add: new_tv_def free_tv_subst dom_def cod_def)

lemma new_tv_id_subst [simp]: "new_tv n id_subst"
by (simp add: id_subst_def new_tv_def free_tv_subst dom_def cod_def)

lemma new_if_subst_type_scheme: "new_tv n (sch::type_scheme) \<Longrightarrow>
    $(\<lambda>k. if k<n then S k else S' k) sch = $S sch"
by (induction sch) simp_all

lemma new_if_subst_type_scheme_list: "new_tv n (A::type_scheme list) \<Longrightarrow>
    $(\<lambda>k. if k<n then S k else S' k) A = $S A"
by (induction A) (simp_all add: new_if_subst_type_scheme)


\<comment> \<open>constructor laws for @{text dom} and @{text cod}\<close>

lemma dom_id_subst [simp]: "dom id_subst = {}"
  unfolding dom_def id_subst_def empty_def by simp

lemma cod_id_subst [simp]: "cod id_subst = {}"
  unfolding cod_def by simp


lemma free_tv_id_subst [simp]: "free_tv id_subst = {}"
  unfolding free_tv_subst by simp

lemma free_tv_nth_A_impl_free_tv_A:
  "\<lbrakk> n < length A;  x : free_tv (A!n) \<rbrakk> \<Longrightarrow> x : free_tv A"
proof (induction A arbitrary: n)
  case Nil thus ?case by simp
next
  case (Cons a A)
  then show ?case by (fastforce simp add:nth_Cons' split: if_splits)
qed

text
\<open>if two substitutions yield the same result if applied to a type
   structure the substitutions coincide on the free type variables
   occurring in the type structure\<close>

lemma typ_substitutions_only_on_free_variables: 
  "(\<forall>x\<in>free_tv t. (S x) = (S' x)) \<Longrightarrow> $ S (t::typ) = $ S' t"
  by (induct t) simp_all

lemma eq_free_eq_subst_te: "(\<forall>n. n\<in>(free_tv t) \<longrightarrow> S1 n = S2 n) \<Longrightarrow> $ S1 (t::typ) = $ S2 t"
apply (rule typ_substitutions_only_on_free_variables)
apply simp
done

lemma scheme_substitutions_only_on_free_variables:
  "(\<forall>x\<in>free_tv sch. (S x) = (S' x)) \<Longrightarrow> $ S (sch::type_scheme) = $ S' sch"
  by (induct sch) simp_all

lemma eq_free_eq_subst_type_scheme: 
  "(\<forall>n. n\<in>(free_tv sch) \<longrightarrow> S1 n = S2 n) \<Longrightarrow> $ S1 (sch::type_scheme) = $ S2 sch"
apply (rule scheme_substitutions_only_on_free_variables)
apply simp
done

lemma eq_free_eq_subst_scheme_list:
  "(\<forall>n. n\<in>(free_tv A) \<longrightarrow> S1 n = S2 n) \<Longrightarrow> $S1 (A::type_scheme list) = $S2 A"
proof (induct A)
  case Nil then show ?case by fastforce
next
  case Cons then show ?case by (fastforce intro: eq_free_eq_subst_type_scheme)
qed

lemma weaken_asm_Un: "((\<forall>x\<in>A. (P x)) \<longrightarrow> Q) \<Longrightarrow> ((\<forall>x\<in>A \<union> B. (P x)) \<longrightarrow> Q)"
  by fast

lemma scheme_list_substitutions_only_on_free_variables:
  "(\<forall>x\<in>free_tv A. (S x) = (S' x)) \<Longrightarrow> $ S (A::type_scheme list) = $ S' A"
by (induction A) (auto simp add: eq_free_eq_subst_type_scheme)

lemma eq_subst_te_eq_free:
  "$ S1 (t::typ) = $ S2 t \<Longrightarrow> n:(free_tv t) \<Longrightarrow> S1 n = S2 n"
  by (induct t) auto

lemma eq_subst_type_scheme_eq_free: 
  "\<lbrakk> $ S1 (sch::type_scheme) = $ S2 sch; n:(free_tv sch) \<rbrakk> \<Longrightarrow> S1 n = S2 n"
by (induction "sch") (auto dest: mk_scheme_injective)

lemma eq_subst_scheme_list_eq_free:
  "\<lbrakk> $S1 (A::type_scheme list) = $S2 A;  n:(free_tv A) \<rbrakk> \<Longrightarrow> S1 n = S2 n"
proof (induct A)
  case Nil
  then show ?case by fastforce
next
  case Cons
  then show ?case by (fastforce intro: eq_subst_type_scheme_eq_free)
qed

lemma codD: "v : cod S \<Longrightarrow> v : free_tv S"
  unfolding free_tv_subst by blast

lemma not_free_impl_id: "x \<notin> free_tv S \<Longrightarrow> S x = TVar x"
  unfolding free_tv_subst dom_def by blast

lemma free_tv_le_new_tv: "[| new_tv n t; m:free_tv t |] ==> m<n"
  unfolding new_tv_def by blast

lemma cod_app_subst:
  "[| v : free_tv(S n); v\<noteq>n |] ==> v : cod S"
by (force simp add: dom_def cod_def UNION_eq Bex_def)


lemma free_tv_subst_var: "free_tv (S (v::nat)) \<subseteq> insert v (cod S)"
apply (cases "v:dom S")
apply (fastforce simp add: cod_def)
apply (fastforce simp add: dom_def)
done

lemma free_tv_app_subst_te: "free_tv ($ S (t::typ)) \<subseteq> cod S \<union> free_tv t"
proof (induct t)
  case (TVar n) then show ?case by (simp add: free_tv_subst_var)
next
  case (Fun t1 t2) then show ?case by fastforce
qed

lemma free_tv_app_subst_type_scheme:
    "free_tv ($ S (sch::type_scheme)) \<subseteq> cod S \<union> free_tv sch"
proof (induct sch)
  case (FVar n)
  then show ?case by (simp add: free_tv_subst_var)
next
  case (BVar n)
  then show ?case by simp
next
  case (SFun t1 t2)
  then show ?case by fastforce
qed

lemma free_tv_app_subst_scheme_list: "free_tv ($ S (A::type_scheme list)) \<subseteq> cod S \<union> free_tv A"
proof (induct A)
  case Nil then show ?case by simp
next
  case (Cons a al)
  with free_tv_app_subst_type_scheme
  show ?case by fastforce
qed

lemma free_tv_comp_subst: 
  "free_tv (\<lambda>u::nat. $ s1 (s2 u) :: typ) \<subseteq>    
    free_tv s1 Un free_tv s2"
unfolding free_tv_subst dom_def
by (force simp add: cod_def dom_def dest!:free_tv_app_subst_te [THEN subsetD])

lemma free_tv_o_subst: 
  "free_tv ($ S1 \<circ> S2) \<subseteq> free_tv S1 \<union> free_tv (S2 :: nat => typ)"
unfolding o_def by (rule free_tv_comp_subst)

lemma free_tv_of_substitutions_extend_to_types:
  "n : free_tv t \<Longrightarrow> free_tv (S n) \<subseteq> free_tv ($ S t::typ)"
by (induct t) auto

lemma free_tv_of_substitutions_extend_to_schemes:
  "n : free_tv sch \<Longrightarrow> free_tv (S n) \<subseteq> free_tv ($ S sch::type_scheme)"
by (induct sch) auto

lemma free_tv_of_substitutions_extend_to_scheme_lists [simp]:
  "n : free_tv A \<Longrightarrow> free_tv (S n) \<subseteq> free_tv ($ S A::type_scheme list)"
by (induct A) (auto dest: free_tv_of_substitutions_extend_to_schemes)

lemma free_tv_ML_scheme:
  fixes sch :: type_scheme
  shows "(n : free_tv sch) = (n: set (free_tv_ML sch))"
by (induct sch) simp_all

lemma free_tv_ML_scheme_list:
  fixes A :: "type_scheme list"
  shows "(n : free_tv A) = (n: set (free_tv_ML A))"
by (induct_tac A) (simp_all add: free_tv_ML_scheme)


\<comment> \<open>lemmata for @{text bound_tv}\<close>

lemma bound_tv_mk_scheme [simp]: "bound_tv (mk_scheme t) = {}"
by (induct t) simp_all

lemma bound_tv_subst_scheme [simp]:
  fixes sch :: type_scheme
  shows "bound_tv ($ S sch) = bound_tv sch"
by (induct sch) simp_all

lemma bound_tv_subst_scheme_list [simp]: 
  fixes A :: "type_scheme list"
  shows "bound_tv ($ S A) = bound_tv A"
by (induct A) simp_all


\<comment> \<open>Lemmata for @{text new_tv}\<close>

lemma new_tv_subst: 
  "new_tv n S = ((\<forall>m. n \<le> m \<longrightarrow> (S m = TVar m)) \<and>  
                 (\<forall>l. l < n \<longrightarrow> new_tv n (S l) ))"
unfolding new_tv_def  free_tv_subst cod_def dom_def
apply rule
 apply force
by simp (meson not_le)

lemma new_tv_list: "new_tv n x = (\<forall>y\<in>set x. new_tv n y)"
by (induction x) simp_all

\<comment> \<open>substitution affects only variables occurring freely\<close>
lemma subst_te_new_tv:
  "new_tv n (t::typ) \<Longrightarrow> $(\<lambda>x. if x=n then t' else S x) t = $S t"
by (induct t) simp_all

lemma subst_te_new_type_scheme:
  "new_tv n (sch::type_scheme) \<Longrightarrow> $(\<lambda>x. if x=n then sch' else S x) sch = $S sch"
by (induct sch) simp_all

lemma subst_tel_new_scheme_list [simp]:
  "new_tv n (A::type_scheme list) \<Longrightarrow> $(\<lambda>x. if x=n then t else S x) A = $S A"
by (induct A) (simp_all add: subst_te_new_type_scheme)


\<comment> \<open>all greater variables are also new\<close>
lemma new_tv_le: 
  "n\<le>m \<Longrightarrow> new_tv n t \<Longrightarrow> new_tv m t"
by (meson less_le_trans new_tv_def)

lemma new_tv_Suc[simp]: "new_tv n t \<Longrightarrow> new_tv (Suc n) t"
by (rule lessI [THEN less_imp_le [THEN new_tv_le]])

\<comment> \<open>@{text new_tv} property remains if a substitution is applied\<close>
lemma new_tv_subst_var: 
  "[| n<m; new_tv m (S::subst) |] ==> new_tv m (S n)"
by (simp add: new_tv_subst)

lemma new_tv_subst_te [simp]:
  "new_tv n S \<Longrightarrow> new_tv n (t::typ) \<Longrightarrow> new_tv n ($ S t)"
by (induction t) (auto simp add: new_tv_subst)

lemma new_tv_subst_scheme_list:
  "new_tv n S \<Longrightarrow> new_tv n (A::type_scheme list) \<Longrightarrow> new_tv n ($ S A)"
by (meson UnE codD free_tv_app_subst_scheme_list in_mono new_tv_def)

lemma new_tv_only_depends_on_free_tv_type_scheme:
  fixes sch :: type_scheme
  shows "free_tv sch = free_tv sch' \<Longrightarrow> new_tv n sch \<Longrightarrow> new_tv n sch'"
  unfolding new_tv_def by simp

lemma new_tv_only_depends_on_free_tv_scheme_list:
  fixes A :: "type_scheme list"
  shows "free_tv A = free_tv A' \<Longrightarrow> new_tv n A \<Longrightarrow> new_tv n A'"
  unfolding new_tv_def by simp

lemma new_tv_nth_nat_A: 
  "m < length A \<Longrightarrow> new_tv n A \<Longrightarrow> new_tv n (A!m)"
unfolding new_tv_def using free_tv_nth_A_impl_free_tv_A by blast


\<comment> \<open>composition of substitutions preserves @{text new_tv} proposition\<close>
lemma new_tv_subst_comp_1: 
  "[| new_tv n (S::subst); new_tv n R |] ==> new_tv n (($ R) \<circ> S)"
by (simp add: new_tv_subst)

lemma new_tv_subst_comp_2 :
  "[| new_tv n (S::subst); new_tv n R |] ==> new_tv n (\<lambda>v.$ R (S v))"
by (simp add: new_tv_subst)

\<comment> \<open>new type variables do not occur freely in a type structure\<close>
lemma new_tv_not_free_tv:
  "new_tv n A \<Longrightarrow> n \<notin> free_tv A"
by (auto simp add: new_tv_def)

lemma fresh_variable_types: "\<exists>n. new_tv n (t::typ)"
apply (unfold new_tv_def)
apply (induction t)
 apply auto[1]
by (metis less_trans linorder_cases new_tv_Fun new_tv_def)


lemma fresh_variable_type_schemes:
  "\<exists>n. new_tv n (sch::type_scheme)"
apply (unfold new_tv_def)
apply (induct_tac sch)
  apply (auto)[1]
 apply simp
by (metis less_trans linorder_cases new_tv_Fun2 new_tv_def)

lemma fresh_variable_type_scheme_lists: 
  "\<exists>n. new_tv n (A::type_scheme list)"
apply (induction A)
 apply (simp)
by (metis fresh_variable_type_schemes le_cases new_tv_Cons new_tv_le)

lemma make_one_new_out_of_two: 
  "[| \<exists>n1. (new_tv n1 x); \<exists>n2. (new_tv n2 y)|] ==> \<exists>n. (new_tv n x) \<and> (new_tv n y)"
by (meson new_tv_le nle_le)

lemma ex_fresh_variable: 
  "\<And>(A::type_scheme list) (A'::type_scheme list) (t::typ) (t'::typ).  
          \<exists>n. (new_tv n A) \<and> (new_tv n A') \<and> (new_tv n t) \<and> (new_tv n t')"
by (meson fresh_variable_type_scheme_lists fresh_variable_types max.cobounded1 max.cobounded2 new_tv_le)

\<comment> \<open>mgu does not introduce new type variables\<close>
lemma mgu_new: 
  "[|mgu t1 t2 = Some u; new_tv n t1; new_tv n t2|] ==> new_tv n u"
by (meson UnE mgu_free new_tv_def subsetD)


(* lemmata for substitutions *)

lemma length_app_subst_list [simp]:
  "\<And>A:: ('a::type_struct) list. length ($ S A) = length A"
unfolding app_subst_list by simp

lemma subst_TVar_scheme [simp]:
  fixes sch :: type_scheme
  shows "$ TVar sch = sch"
by (induct sch) simp_all

lemma subst_TVar_scheme_list [simp]:
  fixes A :: "type_scheme list"
  shows "$ TVar A = A"
by (induct A) (simp_all add: app_subst_list)

\<comment> \<open>application of @{text id_subst} does not change type expression\<close>
lemma app_subst_id_te [simp]: "$ id_subst = (\<lambda>t::typ. t)"
by (metis id_subst_def mk_scheme_injective subst_TVar_scheme subst_mk_scheme)

lemma app_subst_id_type_scheme [simp]:
  "$ id_subst = (\<lambda>sch::type_scheme. sch)"
using id_subst_def subst_TVar_scheme by auto


\<comment> \<open>application of @{text id_subst} does not change list of type expressions\<close>
lemma app_subst_id_tel [simp]: 
  "$ id_subst = (\<lambda>A::type_scheme list. A)"
using id_subst_def subst_TVar_scheme_list by auto

\<comment> \<open>composition of substitutions\<close>
lemma o_id_subst [simp]: "$S \<circ> id_subst = S"
unfolding id_subst_def o_def by simp

lemma subst_comp_te: "$ R ($ S t::typ) = $ (\<lambda>x. $ R (S x) ) t"
by (induct t) simp_all

lemma subst_comp_type_scheme: 
  "$ R ($ S sch::type_scheme) = $ (\<lambda>x. $ R (S x) ) sch"
by (induct sch) simp_all

lemma subst_comp_scheme_list: 
  "$ R ($ S A::type_scheme list) = $ (\<lambda>x. $ R (S x)) A"
unfolding app_subst_list
proof (induct A)
  case Nil thus ?case by simp
next
  case Cons thus ?case by (simp add: subst_comp_type_scheme)
qed

lemma nth_subst: 
  "n < length A \<Longrightarrow> ($ S A)!n = $S (A!n)"
by (simp add: app_subst_list)

end
