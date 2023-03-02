section \<open>Examples of Rensets and Renaming-Based Recursion\<close>

theory Examples
  imports FRBCE_Rensets Rensets 
begin 

subsection \<open>Variables and terms as rensets\<close>

text \<open>Variables form a renset: \<close>
interpretation Var: Renset where vsubstA = "vss"  
  unfolding Renset_def vss_def by auto

text \<open>Terms form a renset: \<close>
interpretation Term: Renset where vsubstA = "\<lambda>t x. vsubst t x"  
  unfolding Renset_def   
	using subst_Vr subst_comp_same  
	using fresh_subst_same subst_chain 
  using subst_commute_diff by auto

text \<open>... and a CE renset: \<close>

interpretation Term: CE_Renset 
  where vsubstA = "\<lambda>t x. subst t (Vr x)"  
    and VrA = Vr and ApA = Ap and LmA = Lm
  apply standard  
  by (auto simp add: Lm_subst_rename fresh_subst_same)


subsection \<open> Interpretation in semantic domains\<close>

type_synonym 'A I = "(var \<Rightarrow> 'A) \<Rightarrow> 'A"

locale Sem_Int = 
  fixes ap :: "'A \<Rightarrow> 'A \<Rightarrow> 'A" and lm :: "('A \<Rightarrow> 'A) \<Rightarrow> 'A"
begin 

(* The target domain is a CE renset: *)
sublocale CE_Renset 
  where vsubstA = "\<lambda>s x y \<xi>. s (\<xi> (y := \<xi> x))"
    and VrA = "\<lambda>x \<xi>. \<xi> x" 
    and ApA = "\<lambda>i1 i2 \<xi>. ap (i1 \<xi>) (i2 \<xi>)"
    and LmA = "\<lambda>x i \<xi>. lm (\<lambda>d. i (\<xi>(x:=d)))"
  by standard (auto simp: fun_eq_iff fun_upd_twist intro!: arg_cong[of _ _ lm]) 

(* ... hence the desired recursive clauses hold: *)
lemmas sem_f_clauses = f_Vr f_Ap f_Lm f_subst f_unique

end (* context Sem_Int *)


subsection \<open> Closure of rensets under functors \<close>

text \<open> A functor applied to a renset yields a renset -- actually, 
a "local functor", i.e., one that is functorial 
w.r.t. functions on the substitutive set's carrier only, suffices. \<close>


locale Local_Functor = 
  fixes Fmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'FA \<Rightarrow> 'FA"
  assumes Fmap_id: "Fmap id = id"
    and Fmap_comp: "Fmap (g o f) = Fmap g o Fmap f"
begin

lemma Fmap_comp': "Fmap (g o f) k = Fmap g (Fmap f k)"
  using Fmap_comp by auto

end (* context Local_Functor *)


locale Renset_plus_Local_Functor = 
  Renset vsubstA + Local_Functor Fmap 
  for vsubstA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" 
    and Fmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'FA \<Rightarrow> 'FA" 
begin

(* The new renset with carrier 'A F: *)
sublocale F: Renset where vsubstA = 
  "\<lambda>k x y. Fmap (\<lambda>a. vsubstA a x y) k" 
  apply standard
  subgoal by (metis Fmap_id eq_id_iff vsubstA_id)
  subgoal unfolding Fmap_comp'[symmetric] o_def by simp
  subgoal unfolding Fmap_comp'[symmetric] o_def  
  	by (simp add: vsubstA_chain)
  subgoal unfolding Fmap_comp'[symmetric] o_def  
    using vsubstA_commute_diff by force .

end (* context Renset_plus_Local_Functor *)


subsection \<open> The length of a term via renaming-based recursion \<close>

(* The target domain is a CE substitutive set: *)
interpretation length : CE_Renset
  where vsubstA = "\<lambda>n x y. n"
    and VrA = "\<lambda>x. 1" 
    and ApA = "\<lambda>n1 n2. max n1 n2 + 1" 
    and LmA = "\<lambda>x n. n + 1"
  apply standard by auto

(* ... hence the desired recursive clauses hold: *)
lemmas length_f_clauses = length.f_Vr length.f_Ap length.f_Lm length.f_subst length.f_unique


subsection \<open> Counting the lambda-abstractions in a term via renaming-based recursion \<close>

(* The target domain is a CE substitutive set: *)
interpretation clam : CE_Renset
  where vsubstA = "\<lambda>n x y. n"
    and VrA = "\<lambda>x. 0" 
    and ApA = "\<lambda>n1 n2. n1 + n2" 
    and LmA = "\<lambda>x n. n + 1"
  apply standard by auto

(* ... hence the desired recursive clauses hold: *)
lemmas clam_f_clauses = clam.f_Vr clam.f_Ap clam.f_Lm clam.f_subst clam.f_unique


subsection \<open> Counting free occurences of a variable in a term via renaming-based recursion \<close>

(* Counting the number of free occurrences of a variable in a term *)
(* The target domain is a CE substitutive set: *)
interpretation cfv : CE_Renset
  where vsubstA = 
    "\<lambda>f z y. \<lambda>x. if x \<notin> {y,z} 
     then f x
     else if x = z \<and> x \<noteq> y then f x + f y 
     else if x = y \<and> x \<noteq> z then (0::nat)
     else f y"
    and VrA = "\<lambda>y. \<lambda>x. if x = y then 1 else 0" 
    and ApA = "\<lambda>f1 f2. \<lambda>x. f1 x + f2 x" 
    and LmA = "\<lambda>y f. \<lambda>x. if x = y then 0 else f x"
  apply standard by (auto simp: fun_eq_iff)

(* ... hence the desired recursive clauses hold: *)
lemmas cfv_f_clauses = cfv.f_Vr cfv.f_Ap cfv.f_Lm cfv.f_subst cfv.f_unique


subsection \<open> Substitution via renaming-based recursion \<close>

(* The target domain is a CE substitutive set: *)
locale Subst = 
  fixes s :: trm and x :: var
begin

sublocale ssb : BCE_Renset
  where vsubstA = "vsubst"
    and VrA = "\<lambda>y. if y = x then s else Vr y" 
    and ApA = "Ap" 
    and LmA = "Lm"
    and X = "FFvars s \<union> {x}"
  apply standard by (auto simp: fun_eq_iff cofinite_fresh Term.LmA_rename) 

(* ... hence the desired recursive clauses hold: *)
lemmas ssb_f_clauses = ssb.f_Vr ssb.f_Ap ssb.f_Lm ssb.f_subst ssb.f_unique

(* We actually already have the substitution operator defined, 
and the one defined above can be proved to be the same as this: *)

lemma subst_eq_ssb: 
  "subst t s x = ssb.f t"
proof-
  have "(\<lambda>t. subst t s x) = ssb.f" 
    apply(rule ssb.f_unique) by auto
  thus ?thesis unfolding fun_eq_iff by auto
qed

end (* context Subst *)


subsection \<open> Parrallel substitution via renaming-based recursion \<close>

(* The target domain is a CE substitutive set: *)
locale PSubst = 
  fixes \<rho> :: fenv
begin

definition X where
  "X = supp \<rho> \<union> \<Union> {FFvars (get \<rho> x) | x . x \<in> supp \<rho>}"

lemma finite_Supp: "finite X" 
  unfolding X_def unfolding finite_Un apply safe
  by (auto simp: finite_supp cofinite_fresh)

sublocale canEta' : BCE_Renset
  where vsubstA = "vsubst"
    and VrA = "\<lambda>y. get \<rho> y" 
    and ApA = "Ap" 
    and LmA = "Lm"
    and X = "X" 
  apply standard
  by (auto simp: fun_eq_iff cofinite_fresh finite_Supp Term.LmA_rename X_def finite_supp)
    (metis fresh_subst_id mem_Collect_eq subst_Vr supp_get)

(* ... hence the desired recursive clauses hold: *)
lemmas canEta'_f_clauses =  canEta'.f_Vr canEta'.f_Ap canEta'.f_Lm canEta'.f_subst canEta'.f_unique

end (* context PSubst *)


subsection \<open> Counting bound variables via renaming-based recursion \<close>

(* Counting the number of bound variables *)

(* This is an instance of the semantic-domain interpretation pattern: *)
interpretation cbvs: Sem_Int where ap = "(+)" and lm = "\<lambda>d. d (1::nat)" .

(* ... hence the desired recursive clauses hold: *)
lemmas cbvs_f_clauses = cbvs.f_Vr cbvs.f_Ap cbvs.f_Lm cbvs.f_subst cbvs.f_unique

definition cbv  :: "trm \<Rightarrow> nat" where 
  "cbv t \<equiv> cbvs.f t (\<lambda>_. 0)"


subsection \<open> Testing eta-reducibility via renaming-based recursion \<close>

(* This is an instance of the semantic-domain interpretation pattern: *)
interpretation canEta': Sem_Int where ap = "(\<and>)" and lm = "\<lambda>d. d True" .

(* ... hence the desired recursive clauses hold: *)
lemmas canEta'_f_clauses = canEta'.f_Vr canEta'.f_Ap canEta'.f_Lm canEta'.f_subst canEta'.f_unique

definition canEta  :: "trm \<Rightarrow> bool" where 
  "canEta t \<equiv> \<exists>x s. t = Lm x (Ap s (Vr x)) \<and> canEta'.f s ((\<lambda>_. True)(x:=False))"


end 
