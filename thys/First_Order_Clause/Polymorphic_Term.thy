theory Polymorphic_Term
  imports 
    IsaFoR_Nonground_Term
    Polymorphic_Ground_Term
begin


section \<open>Polymorphic terms\<close>

datatype ('f, poly_term_vars: 'v, 'tyf, poly_term_type_vars: 'tyv) poly_term =
  PVar (the_PVar: 'v) |
  PFun
    (fun_sym: 'f) (type_args: "('tyf, 'tyv) term list")
    (args: "('f, 'v, 'tyf, 'tyv) poly_term list")
where
  "args (PVar _) = []"

type_synonym ('f, 'v, 'tyf, 'tyv) poly_subst = 
  "('v \<Rightarrow> ('f, 'v, 'tyf, 'tyv) poly_term) \<times> ('tyv \<Rightarrow> ('tyf, 'tyv) term)"

primrec poly_term_subst ::
  "('f, 'v, 'tyf, 'tyv) poly_term \<Rightarrow>
   ('f, 'v, 'tyf, 'tyv) poly_subst \<Rightarrow>
   ('f, 'v, 'tyf, 'tyv) poly_term" (infixl \<open>\<cdot>p\<close> 67) where
  "PVar x \<cdot>p \<sigma> = fst \<sigma> x"
| "PFun f \<alpha>s ts \<cdot>p \<sigma> = PFun f (map (\<lambda>\<alpha>. \<alpha> \<cdot> snd \<sigma>) \<alpha>s) (map (\<lambda>t. t \<cdot>p \<sigma>) ts)"

definition compose_subst (infixl \<open>\<odot>\<close> 70) where
  "\<sigma> \<odot> \<sigma>' \<equiv> (\<lambda>x. PVar x \<cdot>p \<sigma> \<cdot>p \<sigma>', snd \<sigma> \<circ>\<^sub>s snd \<sigma>')"

fun update_subst :: 
  "('f, 'v, 'tyf, 'tyv) poly_subst \<Rightarrow>
   'v \<Rightarrow>
   ('f, 'v, 'tyf, 'tyv) poly_term \<Rightarrow>
   ('f, 'v, 'tyf, 'tyv) poly_subst" (\<open>_\<lbrakk>_ := _\<rbrakk>\<close> [1000, 0, 50] 70) where
  "update_subst (\<sigma>, \<sigma>') x update = (\<sigma>(x:=update), \<sigma>')"

abbreviation id_subst where
  "id_subst \<equiv> (PVar, Var)"

abbreviation apply_subst (infixl "\<cdot>v" 69) where
  "apply_subst x \<sigma> \<equiv> PVar x \<cdot>p \<sigma>"

abbreviation poly_term_is_ground where
  "poly_term_is_ground t \<equiv> poly_term_vars t = {} \<and> poly_term_type_vars t = {}"

fun poly_to_ground ::  "('f, 'v, 'tyf, 'tyv) poly_term \<Rightarrow> ('f, 'tyf) poly_gterm" where
  "poly_to_ground (PFun f \<alpha>s ts) = PGFun f (map term.to_ground \<alpha>s) (map poly_to_ground ts)"

fun poly_from_ground :: "('f, 'tyf) poly_gterm \<Rightarrow> ('f, 'v, 'tyf, 'tyv) poly_term" where
  "poly_from_ground (PGFun f \<alpha>s ts) = PFun f (map term.from_ground \<alpha>s) (map poly_from_ground ts)"

abbreviation is_PVar where
 "is_PVar t \<equiv> \<exists>x. t = PVar x"

abbreviation is_PFun where
  "is_PFun t \<equiv> \<not>is_PVar t"

lemma is_PFunE [elim]:
  "is_PFun t \<Longrightarrow> (\<And>f \<alpha>s ts. t = PFun f \<alpha>s ts \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) auto

lemma subst_id_subst [simp]: "t \<cdot>p id_subst = t"
  by (induction t) (auto simp: list.map_ident_strong)

lemma subst_two: "t \<cdot>p \<sigma> \<cdot>p \<sigma>' = t \<cdot>p (\<lambda>x. fst \<sigma> x \<cdot>p \<sigma>', snd \<sigma> \<circ>\<^sub>s snd \<sigma>')"
  by (induction t) auto

lemma poly_term_subst_eq_conv:
  "t \<cdot>p (\<sigma>, \<sigma>') = t \<cdot>p (\<tau>, \<tau>') \<longleftrightarrow>
    (\<forall>x \<in> poly_term_vars t. \<sigma> x = \<tau> x) \<and> (\<forall>x \<in> poly_term_type_vars t. \<sigma>' x = \<tau>' x)"
  by (induction t) (auto simp: term_subst_eq_conv)

lemma obtain_PFun_not_in_finite_set:
  fixes T :: "('f, 'v, 'tyf, 'tyv) poly_term set" 
  assumes "finite T"
  shows "\<exists>t. t \<notin> T \<and> is_PFun t"
proof -

  define arg_lengths where
    "arg_lengths \<equiv> length ` poly_term.args ` {t \<in> T. is_PFun t}"

  then have "finite arg_lengths"
    using assms
    unfolding arg_lengths_def
    by auto

  then obtain n where n: "\<forall>n' \<in> arg_lengths. n' < n"
    using finite_nat_set_iff_bounded
    by auto

  define t :: "('f, 'v, 'tyf, 'tyv) poly_term" where
    "t = PFun (SOME f. True) [] (replicate n (PFun (SOME f. True) [] []))"

  show ?thesis
  proof (intro exI conjI)
    show "t \<notin> T"
      using n
      unfolding t_def arg_lengths_def
      by auto
  next
    show "is_PFun t"
      unfolding t_def
      by simp
  qed
qed

lemma poly_term_type_vars_subst_update:
  fixes t
  assumes "poly_term_type_vars u = {}"
  shows "poly_term_type_vars (t \<cdot>p \<sigma>\<lbrakk>x := u\<rbrakk>) \<subseteq> poly_term_type_vars (t \<cdot>p \<sigma>)"
  using assms
proof (induction t)
  case (PVar x)
  then show ?case
    by (cases \<sigma>) auto
next
  case (PFun f \<alpha>s ts)
  then show ?case
    by (cases \<sigma>) fastforce
qed


subsection \<open>Substitution interpretations\<close>

global_interpretation poly_term: base_substitution where
  subst = "(\<cdot>p)" and vars = poly_term_vars and id_subst = id_subst and
  comp_subst = "(\<odot>)" and apply_subst = "(\<cdot>v)" and is_ground = poly_term_is_ground
proof unfold_locales
  fix t and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "t \<cdot>p \<sigma>\<^sub>1 \<odot> \<sigma>\<^sub>2 = t \<cdot>p \<sigma>\<^sub>1 \<cdot>p \<sigma>\<^sub>2"
    unfolding compose_subst_def
    by (induction t) auto
next
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "\<sigma>\<^sub>1 \<odot> \<sigma>\<^sub>2 \<odot> \<sigma>\<^sub>3 = \<sigma>\<^sub>1 \<odot> (\<sigma>\<^sub>2 \<odot> \<sigma>\<^sub>3)"
    unfolding compose_subst_def
    by (simp add: subst_two term.comp_subst.left.assoc)
next
  fix t :: "('f, 'v, 'tyf, 'tyv) poly_term"
  assume "poly_term_is_ground t"  
  
  then show "\<forall>\<sigma>. t \<cdot>p \<sigma> = t"
  proof (induction t)
    case (PVar x)

    then show ?case
      by simp
  next
    case (PFun f \<alpha>s ts)

    moreover have "\<And>\<sigma>. map (\<lambda>\<alpha>. \<alpha> \<cdot> \<sigma>) \<alpha>s = \<alpha>s"
      using PFun(2)
      by (induction \<alpha>s) auto

    moreover have "\<And>\<sigma> \<sigma>'. map (\<lambda>t. t \<cdot>p (\<sigma>, \<sigma>')) ts = ts"
      using PFun
      by (induction ts) auto

    ultimately show ?case
      by simp
  qed
next
  fix t and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "t \<cdot>p \<sigma>\<^sub>1 \<odot> \<sigma>\<^sub>2 = t \<cdot>p \<sigma>\<^sub>1 \<cdot>p \<sigma>\<^sub>2"
    unfolding compose_subst_def
    by (induction t) auto
next
  fix t and \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "poly_term_vars (t \<cdot>p \<sigma>) = \<Union> (poly_term_vars ` (\<lambda>x. PVar x \<cdot>p \<sigma>) ` poly_term_vars t)"
    by (induction t) auto
next
  fix t and \<gamma> :: "('f, 'v, 'tyf, 'tyv) poly_subst"
  assume "poly_term_is_ground (t \<cdot>p \<gamma>)"

  then show "\<forall>x\<in>poly_term_vars t. poly_term_is_ground (x \<cdot>v \<gamma>)"
    by (induction t) auto
qed (auto simp: compose_subst_def)

global_interpretation poly_term: subst_update where
  subst = "(\<cdot>p)" and vars = poly_term_vars and id_subst = id_subst and
  is_ground = poly_term_is_ground and apply_subst = "(\<cdot>v)" and 
  comp_subst = "(\<odot>)" and subst_update = update_subst
proof unfold_locales
  fix x update and \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "x \<cdot>v \<sigma>\<lbrakk>x := update\<rbrakk> = update"
    by (cases \<sigma>) simp
next
  fix \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst" and x y :: 'v and update

  assume "x \<noteq> y"

  then show "x \<cdot>v \<sigma>\<lbrakk>y := update\<rbrakk> = x \<cdot>v \<sigma>"
    by (cases \<sigma>) simp
next
  fix x update \<sigma> and t :: "('f, 'v, 'tyf, 'tyv) poly_term"

  assume "x \<notin> poly_term_vars t"

  then show "t \<cdot>p \<sigma>\<lbrakk>x := update\<rbrakk> = t \<cdot>p \<sigma>"
    by (cases \<sigma>, induction t) simp_all
next
  fix \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst" and x
  
  show "\<sigma>\<lbrakk>x := x \<cdot>v \<sigma>\<rbrakk> = \<sigma>"
    by (cases \<sigma>) simp
next
  fix \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst" and x t t'

  show "(\<sigma>\<lbrakk>x := t\<rbrakk>)\<lbrakk>x := t'\<rbrakk> = \<sigma>\<lbrakk>x := t'\<rbrakk>"
    by (cases \<sigma>) simp
qed

global_interpretation poly_term: finite_variables where
  subst = "(\<cdot>p)" and vars = poly_term_vars and id_subst = id_subst and
  is_ground = poly_term_is_ground and apply_subst = "(\<cdot>v)" and 
  comp_subst = "(\<odot>)"
  by unfold_locales simp

(* TODO: Do without infinite when Unification exists *)
global_interpretation poly_term: base_variables_in_base_imgu where
  subst = "(\<cdot>p)" and id_subst = id_subst and is_ground = poly_term_is_ground and
  vars = "poly_term_vars :: ('f, 'v, 'tyf, 'tyv) poly_term \<Rightarrow> 'v :: infinite set" and
  apply_subst = "(\<cdot>v)" and comp_subst = "(\<odot>)" and subst_update = update_subst
proof unfold_locales

  show "infinite (UNIV :: 'v set)"
    using infinite_UNIV 
    by simp
next
  fix t and \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst"

  show "\<exists>x. t \<cdot>p \<sigma> = x \<cdot>v id_subst \<Longrightarrow> \<exists>x. t = x \<cdot>v id_subst"
    by (cases t) auto
qed

(* TODO: get rid of infinite *)
global_interpretation poly_term: nonground_term where
  term_subst = "(\<cdot>p)" and id_subst = id_subst and
  term_vars = "poly_term_vars :: ('f, 'v, 'tyf, 'tyv) poly_term \<Rightarrow> 'v :: infinite set" and
  term_is_ground = poly_term_is_ground and apply_subst = "(\<cdot>v)" and comp_subst = "(\<odot>)" and
  subst_update = update_subst and term_from_ground = poly_from_ground and
  term_to_ground = poly_to_ground
proof unfold_locales                                       
  fix t :: "('f, 'v, 'tyf, 'tyv) poly_term"

  show "poly_term_is_ground t \<longleftrightarrow> (\<forall>\<sigma>. t \<cdot>p \<sigma> = t)"
  proof (induction t)
    case (PVar x)

    then show ?case
      by auto
  next
    case (PFun f \<alpha>s ts)

    show ?case 
    proof (rule iffI)
      assume "poly_term_is_ground (PFun f \<alpha>s ts)"

      then show " \<forall>\<sigma>. PFun f \<alpha>s ts \<cdot>p \<sigma> = PFun f \<alpha>s ts"
        using poly_term.subst_ident_if_ground
        by blast
    next
      assume subst_ident: "\<forall>\<sigma>. PFun f \<alpha>s ts \<cdot>p \<sigma> = PFun f \<alpha>s ts"

     {
        fix t
        assume "t \<in> set ts"

        moreover then have "\<forall>\<sigma>. t \<cdot>p \<sigma> = t"
          using subst_ident map_eq_conv 
          by fastforce

        ultimately have "poly_term_is_ground t"
          using PFun
          by presburger
      }

      moreover {
        fix \<alpha>

        assume "\<alpha> \<in> set \<alpha>s"

        moreover then have "\<forall>\<sigma>. \<alpha> \<cdot> \<sigma> = \<alpha>"
          using subst_ident map_eq_conv
          by (metis (no_types, lifting) list.map_ident poly_term.inject(2)
              poly_term_subst.simps(2) prod.collapse prod.simps(1))

        ultimately have "term.is_ground \<alpha>"
          by (meson term.all_subst_ident_iff_ground)
      }

      ultimately show "poly_term_is_ground (PFun f \<alpha>s ts)"
        by auto
    qed
  qed
next

  {
    fix t :: "('f, 'v, 'tyf, 'tyv) poly_term"
    assume t_is_ground: "poly_term_is_ground t"

    have "\<exists>g. poly_from_ground g = t"
    proof(intro exI)

      from t_is_ground
      show "poly_from_ground (poly_to_ground t) = t"
        by (induction t) (simp_all add: map_idI)
    qed
  }

  moreover have "poly_term_is_ground (poly_from_ground t)" for t :: "('f, 'tyf) poly_gterm"
    by (induction t) simp

  ultimately show
    "{t :: ('f, 'v, 'tyf, 'tyv) poly_term. poly_term_is_ground t} = range poly_from_ground"
    by fast
next
  fix t\<^sub>G :: "('f, 'tyf) poly_gterm"


  show "poly_to_ground (poly_from_ground t\<^sub>G) = t\<^sub>G"
    by (induction t\<^sub>G) (auto simp: map_idI)
next
  fix t :: "('f, 'v, 'tyf, 'tyv) poly_term" and ts :: "('f, 'v, 'tyf, 'tyv) poly_term set"

  assume "finite ts" "\<not>poly_term_is_ground t"

  then show "\<exists>\<sigma>. t \<cdot>p \<sigma> \<noteq> t \<and> t \<cdot>p \<sigma> \<notin> ts"
  proof(induction t arbitrary: ts)
    case (PVar x)

    obtain t' where t': "t' \<notin> ts" "is_PFun t'"
      using PVar.prems(1)
      by (metis PVar.prems(1) obtain_PFun_not_in_finite_set)

    define \<sigma> :: "('f, 'v, 'tyf, 'tyv) poly_subst" where "\<sigma> \<equiv> (\<lambda>x. t', Var)"

    have "PVar x \<cdot>p \<sigma> \<noteq> PVar x"
      using t'
      unfolding \<sigma>_def
      by auto

    moreover have "PVar x \<cdot>p \<sigma> \<notin> ts"
      using t'
      unfolding \<sigma>_def
      by simp

    ultimately show ?case
      using PVar
      by blast
  next
    case (PFun f \<alpha>s args)

    show ?case
    proof (cases "\<exists>a \<in> set args. \<not>poly_term_is_ground a")
      case True

      obtain a where a: "a \<in> set args" and a_vars: "\<not>poly_term_is_ground a"
        using True
        by auto

      then obtain \<sigma> where
        \<sigma>: "a \<cdot>p \<sigma> \<noteq> a" and
        a_\<sigma>_not_in_args: "a \<cdot>p \<sigma> \<notin> \<Union> (set ` poly_term.args ` ts)"
        by (metis PFun.IH PFun.prems(1) List.finite_set finite_UN finite_imageI)

      then have "PFun f \<alpha>s args \<cdot>p \<sigma> \<noteq> PFun f \<alpha>s args"
        using a map_eq_conv
        by fastforce

      moreover have "PFun f \<alpha>s args \<cdot>p \<sigma> \<notin> ts"
        using a a_\<sigma>_not_in_args
        by auto

      ultimately show ?thesis
        by blast
    next
      case False

      then obtain \<alpha> where \<alpha>: "\<alpha> \<in> set \<alpha>s" and \<alpha>_vars: "\<not>term.is_ground \<alpha>"
        using PFun(3)
        by auto

      then obtain \<sigma> where
        \<sigma>: "\<alpha> \<cdot> \<sigma> \<noteq> \<alpha>" and
        \<alpha>_\<sigma>_not_in_args: "\<alpha> \<cdot> \<sigma> \<notin> \<Union> (set ` poly_term.type_args ` ts)"
        by (metis PFun.prems(1) UN_simps(10) finite_UN list.set_finite term.exists_non_ident_subst)

      then have "PFun f \<alpha>s args \<cdot>p (PVar, \<sigma>) \<noteq> PFun f \<alpha>s args"
        using \<alpha> map_eq_conv
        by fastforce

      moreover have "PFun f \<alpha>s args \<cdot>p (PVar, \<sigma>) \<notin> ts"
        using \<alpha> \<alpha>_\<sigma>_not_in_args
        by auto

      ultimately show ?thesis
        by blast
    qed    
  qed
next
  fix \<rho> :: "('f, 'v, 'tyf, 'tyv) poly_subst" and t

  assume \<rho>: "poly_term.is_renaming \<rho>"

  then show "inj (\<lambda>x. x \<cdot>v \<rho>) \<and> (\<forall>x. \<exists>x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst)"
    unfolding poly_term.is_renaming_def inj_def
    by (metis poly_term.exhaust poly_term.inject(1) poly_term.simps(4) poly_term.subst_comp_subst 
        poly_term_subst.simps(2) subst_id_subst)

  then have x': "\<And>x. \<exists>x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst"
    by auto

  show "poly_term_vars (t \<cdot>p \<rho>) = poly_term.rename \<rho> ` poly_term_vars t"
  proof (induction t)
    case (PVar x)

    have "x \<cdot>v \<rho> = PVar (poly_term.rename \<rho> x)"
      using x'[of x]
      unfolding poly_term.rename_def[OF \<rho>]
      by auto

    then show ?case
      by simp
  next
    case (PFun f \<alpha>s ts)
    then show ?case
      by auto
  qed
next
  fix u t :: "('f, 'v, 'tyf, 'tyv) poly_term" and \<gamma> x
  assume "poly_term_is_ground u" "poly_term_is_ground (t \<cdot>p \<gamma>)" "x \<in> poly_term_vars t"

  then show "poly_term_is_ground (t \<cdot>p \<gamma>\<lbrakk>x := u\<rbrakk>)"
  proof (induction t)
    case (PVar y)

    then show ?case 
      by (cases \<gamma>) auto
  next
    case (PFun f \<alpha>s ts)

    have "poly_term_type_vars (PFun f \<alpha>s ts \<cdot>p \<gamma>\<lbrakk>x := u\<rbrakk>) = {}"
      using PFun.prems PFun.IH
      by (cases \<gamma>) (metis poly_term_type_vars_subst_update  subset_empty)        
    
    then show ?case
      using PFun(2, 3)
      by (cases \<gamma>) (auto simp: poly_term.base_vars_subst)
  qed
next

  show "\<exists>t. poly_term_is_ground t"
    by (rule exI[of _ "PFun (SOME f. True) [] []"]) simp
next

  let ?upd = "\<lambda>(x, b) \<sigma>. \<sigma>\<lbrakk>x := b\<rbrakk>"

  have snd_fold: "snd (fold ?upd us \<sigma>) = snd \<sigma>" for us and \<sigma> :: "('f,'v,'tyf,'tyv) poly_subst"
  proof (induction us arbitrary: \<sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a us)

    show ?case
      using Cons
      by (cases a, cases \<sigma>) auto
  qed

  fix us us' :: "('v \<times> ('f, 'v, 'tyf, 'tyv) poly_term) list"

  assume "\<And>x. x \<cdot>v fold ?upd us id_subst \<odot> fold ?upd us' id_subst = x \<cdot>v id_subst"

  then have "fst (fold ?upd us id_subst \<odot> fold ?upd us' id_subst) = PVar"
    unfolding compose_subst_def
    by auto

  moreover have "snd (fold ?upd us id_subst \<odot> fold ?upd us' id_subst) = Var"
    by (simp add: compose_subst_def snd_fold)

  ultimately show "fold ?upd us id_subst \<odot> fold ?upd us' id_subst = id_subst"
    unfolding compose_subst_def
    by auto
qed


subsection \<open>Generic term interpretations\<close>

interpretation poly_term: term_interpretation where
  subterms = args and fun_sym = fun_sym and extra = type_args and is_var = poly_term.is_Var and
  Fun = PFun and size = size
proof unfold_locales
  fix t' t :: "('f, 'v, 'tyf, 'tyv) poly_term"
  assume "t' \<in> set (poly_term.args t)"

  then show "size t' < size t"
    by (induction t) (auto simp: elem_size_size_list_size less_Suc_eq trans_less_add2)
next
  fix t :: "('f, 'v :: infinite, 'tyf, 'tyv) poly_term"

  show "\<not> poly_term.is_Var t \<longleftrightarrow> (\<exists>f e ts. t = PFun f e ts)"
  proof (induction t)
    case (PVar x)
    then show ?case 
      by (metis poly_term.set_intros(3) poly_term.distinct(1) fst_conv all_not_in_conv
          poly_term_subst.simps(1))
  next
    case (PFun f \<alpha>s ts)
    then show ?case 
      by simp
  qed
qed fastforce+


end
