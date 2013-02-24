theory FMap
  imports Main "~~/src/HOL/Quotient_Examples/FSet" "~~/src/HOL/Library/DAList"
begin

subsubsection {* The type of finite maps *}

typedef ('a, 'b) fmap  (infixr "f\<rightharpoonup>" 1) = "{x :: 'a \<rightharpoonup> 'b. finite (dom x) }"
  proof show "empty \<in> {x. finite (dom x)}" by simp qed

setup_lifting type_definition_fmap

lift_definition fdom :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key set" is "dom" ..

lift_definition fran :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'value set" is "ran" ..

lift_definition lookup :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value option" is "(\<lambda> x. x)" ..

abbreviation the_lookup (infix "f!" 55)
  where "m f! x \<equiv> the (lookup m x)"

lift_definition fempty :: "'key f\<rightharpoonup> 'value" ("f\<emptyset>") is Map.empty by simp

lemma fempty_fdom[simp]: "fdom f\<emptyset> = {}"
  by (transfer, auto)

lemma fdomIff: "(a : fdom m) = (lookup m a \<noteq> None)"
 by (transfer, auto)

lemma lookup_not_fdom: "x \<notin> fdom m \<Longrightarrow> lookup m x = None"
  by (auto iff:fdomIff)

lemma finite_range:
  assumes "finite (dom m)"
  shows "finite (ran m)"
  apply (rule finite_subset[OF _ finite_imageI[OF assms, of "\<lambda> x . the (m x)"]])
  by (auto simp add: ran_def dom_def image_def)

lemma finite_fdom[simp]: "finite (fdom m)"
  by transfer

lemma finite_fran[simp]: "finite (fran m)"
  by (transfer, rule finite_range)

lemma fmap_eqI[intro]:
  assumes "fdom a = fdom b"
  and "\<And> x. x \<in> fdom a \<Longrightarrow> a f! x = b f! x"
  shows "a = b"
using assms
proof(transfer)
  fix a b :: "'a \<rightharpoonup> 'b"
  assume d: "dom a = dom b"
  assume eq: "\<And> x. x \<in> dom a \<Longrightarrow> the (a x) = the (b x)"
  show "a = b"
  proof
    fix x
    show "a x = b x"
    proof(cases "a x")
    case None
      hence "x \<notin> dom a" by (simp add: dom_def)
      hence "x \<notin> dom b" using d by simp
      hence " b x = None"  by (simp add: dom_def)
      thus ?thesis using None by simp
    next
    case (Some y)
      hence d': "x \<in> dom ( a)" by (simp add: dom_def)
      hence "the ( a x) = the ( b x)" using eq by auto
      moreover
      have "x \<in> dom ( b)" using Some d' d by simp
      then obtain y' where " b x = Some y'" by (auto simp add: dom_def)
      ultimately
      show " a x =  b x" using Some by auto
    qed
  qed
qed

subsubsection {* Updates *}

lift_definition
  fmap_upd :: "'key f\<rightharpoonup> 'value \<Rightarrow> 'key \<Rightarrow> 'value \<Rightarrow> 'key f\<rightharpoonup> 'value" ("_'(_ f\<mapsto> _')" [900,900]900)
  is "\<lambda> m x v. m( x \<mapsto> v)"  by simp

lemma fmap_upd_fdom[simp]: "fdom (h (x f\<mapsto> v)) = insert x (fdom h)"
  by (transfer, auto)

lemma the_lookup_fmap_upd[simp]: "lookup (h (x f\<mapsto> v)) x = Some v"
  by (transfer, auto)

lemma the_lookup_fmap_upd_other[simp]: "x' \<noteq> x \<Longrightarrow> lookup (h (x f\<mapsto> v)) x' = lookup h x'"
  by (transfer, auto)

lemma fmap_upd_overwrite[simp]: "f (x f\<mapsto> y) (x f\<mapsto> z) = f (x f\<mapsto> z)"
  by (transfer, auto) 

lemma fmap_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a f\<mapsto> b))(c f\<mapsto> d) = (m(c f\<mapsto> d))(a f\<mapsto> b)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "x = a", auto)
  apply (case_tac "x = c", auto)
  done

subsubsection {* Restriction *}

lift_definition fmap_restr :: "'a set \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is "\<lambda> S m. (if finite S then (restrict_map m S) else empty)" by auto

lemma lookup_fmap_restr[simp]: "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> lookup (fmap_restr S m) x = lookup m x"
  by (transfer, auto)

lemma fdom_fmap_restr[simp]: "finite S \<Longrightarrow> fdom (fmap_restr S m) = fdom m \<inter> S"
  by (transfer, simp)

lemma fmap_restr_fmap_restr[simp]:
 "finite d1 \<Longrightarrow> finite d2 \<Longrightarrow> fmap_restr d1 (fmap_restr d2 x) = fmap_restr (d1 \<inter> d2) x"
 by (transfer, auto simp add: restrict_map_def)

lemma fmap_restr_fmap_restr_subset:
 "finite d2 \<Longrightarrow> d1 \<subseteq> d2 \<Longrightarrow> fmap_restr d1 (fmap_restr d2 x) = fmap_restr d1 x"
 by (metis Int_absorb2 finite_subset fmap_restr_fmap_restr)

lemma fmap_restr_useless: "finite S \<Longrightarrow> fdom m \<subseteq> S \<Longrightarrow> fmap_restr S m = m"
  by (rule fmap_eqI, auto)

lemma fmap_restr_not_finite:
  "\<not> finite S \<Longrightarrow> fmap_restr S \<rho> = f\<emptyset>"
  by (transfer, simp)

lemma fmap_restr_fmap_upd: "x \<in> S \<Longrightarrow> finite S \<Longrightarrow> fmap_restr S (m1(x f\<mapsto> v)) = (fmap_restr S m1)(x f\<mapsto> v)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "xa = x")
  apply auto
  done

subsubsection {* Deleting *}

lift_definition fmap_delete :: "'a \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is "\<lambda> x m. m(x := None)" by auto

lemma fdom_fmap_delete[simp]:
  "fdom (fmap_delete x m) = fdom m - {x}"
  by (transfer, auto)

lemma fmap_delete_fmap_upd[simp]:
  "fmap_delete x (m(x f\<mapsto> v)) = fmap_delete x m"
  by (transfer, simp)

lemma fmap_delete_noop:
  "x \<notin> fdom m \<Longrightarrow> fmap_delete x m = m"
  by (transfer, auto)

lemma fmap_upd_fmap_delete[simp]: "x \<in> fdom \<Gamma> \<Longrightarrow> (fmap_delete x \<Gamma>)(x f\<mapsto> \<Gamma> f! x) = \<Gamma>"
  by (transfer, auto)

lemma fran_fmap_upd[simp]:
  "fran (m(x f\<mapsto> v)) = insert v (fran (fmap_delete x m))"
by (transfer, auto simp add: ran_def)
 
subsubsection {* Addition (merging) of finite maps *}

lift_definition fmap_add :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b" (infixl "f++" 100) 
  is "map_add" by auto

lemma fdom_fmap_add[simp]: "fdom (m1 f++ m2) = fdom m1 \<union> fdom m2"
  by (transfer, auto)

lemma lookup_fmap_add1[simp]: "x \<in> fdom m2 \<Longrightarrow> lookup (m1 f++ m2) x = lookup m2 x"
  by (transfer, auto)

lemma lookup_fmap_add2[simp]:  "x \<notin> fdom m2 \<Longrightarrow> lookup (m1 f++ m2) x = lookup m1 x"
  apply transfer
  by (metis map_add_dom_app_simps(3))

lemma [simp]: "\<rho> f++ f\<emptyset> = \<rho>"
  by (transfer, auto)

lemma fmap_add_overwrite: "fdom m1 \<subseteq> fdom m2 \<Longrightarrow> m1 f++ m2 = m2"
  apply transfer
  apply rule
  apply (case_tac "x \<in> dom m2")
  apply (auto simp add: map_add_dom_app_simps(1))
  done

lemma fmap_add_upd_swap: 
  "x \<notin> fdom \<rho>' \<Longrightarrow> \<rho>(x f\<mapsto> z) f++ \<rho>' = (\<rho> f++ \<rho>')(x f\<mapsto> z)"
  apply transfer
  by (metis map_add_upd_left)

lemma fmap_add_upd: 
  "\<rho> f++ (\<rho>'(x f\<mapsto> z)) = (\<rho> f++ \<rho>')(x f\<mapsto> z)"
  apply transfer
  by (metis map_add_upd)

lemma fmap_restr_add: "fmap_restr S (m1 f++ m2) = fmap_restr S m1 f++ fmap_restr S m2"
  apply (cases "finite S")
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "x \<in> fdom m2")
  apply auto
  apply (simp add: fmap_restr_not_finite)
  done

subsubsection {* Conversion from associative lists *}

lift_definition fmap_of :: "('a \<times> 'b) list \<Rightarrow> 'a f\<rightharpoonup> 'b"
  is map_of by (rule finite_dom_map_of)

lemma fmap_of_Nil[simp]: "fmap_of [] = f\<emptyset>"
 by (transfer, simp)

lemma fmap_of_Cons[simp]: "fmap_of (p # l) = (fmap_of l)(fst p f\<mapsto> snd p)" 
  by (transfer, simp)

lemma fmap_of_append[simp]: "fmap_of (l1 @ l2) = fmap_of l2 f++ fmap_of l1"
  by (transfer, simp)

lemma lookup_fmap_of[simp]:
  "lookup (fmap_of m) x = map_of m x"
  by (transfer, auto)

lemma fmap_delete_fmap_of[simp]:
  "fmap_delete x (fmap_of m) = fmap_of (AList.delete x m)"
  by (transfer, metis delete_conv')

subsubsection {* Less-than-relation for extending finite maps *}

instantiation fmap :: (type,type) order
begin
  definition "\<rho> \<le> \<rho>' = ((fdom \<rho> \<subseteq> fdom \<rho>') \<and> (\<forall>x \<in> fdom \<rho>. lookup \<rho> x = lookup \<rho>' x))"
  definition "(\<rho>::'a f\<rightharpoonup> 'b) < \<rho>' = (\<rho> \<noteq> \<rho>' \<and> \<rho> \<le> \<rho>')"

  lemma fmap_less_eqI[intro]:
    assumes assm1: "fdom \<rho> \<subseteq> fdom \<rho>'"
      and assm2:  "\<And> x. \<lbrakk> x \<in> fdom \<rho> ; x \<in> fdom \<rho>'  \<rbrakk> \<Longrightarrow> \<rho> f! x = \<rho>' f! x "
     shows "\<rho> \<le> \<rho>'"
   unfolding less_eq_fmap_def
   apply rule
   apply fact
   apply rule+
   apply (frule subsetD[OF `_ \<subseteq> _`])
   apply (frule  assm2)
   apply (auto iff: fdomIff)
   done
  
  lemma fmap_less_eqD:
    assumes "\<rho> \<le> \<rho>'"
    assumes "x \<in> fdom \<rho>"
    shows "lookup \<rho> x = lookup \<rho>' x"
    using assms
    unfolding less_eq_fmap_def by auto
  
  lemma fmap_antisym: assumes  "(x:: 'a f\<rightharpoonup> 'b) \<le> y" and "y \<le> x" shows "x = y "
  proof(rule fmap_eqI[rule_format])
      show "fdom x = fdom y" using `x \<le> y` and `y \<le> x` unfolding less_eq_fmap_def by auto
      
      fix v
      assume "v \<in> fdom x"
      hence "v \<in> fdom y" using `fdom _ = _` by simp
  
      thus "x f! v = y f! v"
        using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by simp
    qed
  
  lemma fmap_trans: assumes  "(x:: 'a f\<rightharpoonup> 'b) \<le> y" and "y \<le> z" shows "x \<le> z"
  proof
    show "fdom x \<subseteq> fdom z" using `x \<le> y` and `y \<le> z` unfolding less_eq_fmap_def
      by -(rule order_trans [of _ "fdom y"], auto)
    
    fix v
    assume "v \<in> fdom x" and "v \<in> fdom z"
    hence "v \<in> fdom y" using `x \<le> y`  unfolding less_eq_fmap_def by auto
    hence "lookup y v = lookup x v"
      using `x \<le> y` `v \<in> fdom x` unfolding less_eq_fmap_def by auto
    moreover
    have "lookup y v = lookup z v"
      by (rule fmap_less_eqD[OF `y \<le> z`  `v \<in> fdom y`])
    ultimately
    show "x f! v = z f! v" by auto
  qed
  
  instance
    apply default
    using fmap_antisym apply (auto simp add: less_fmap_def)[1]
    apply (auto simp add: less_eq_fmap_def)[1]
    using fmap_trans apply assumption
    using fmap_antisym apply assumption
    done
end

lemma fmap_less_fdom:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> fdom \<rho>1 \<subseteq> fdom \<rho>2"
  by (metis less_eq_fmap_def)

lemma fmap_less_restrict:
  "\<rho>1 \<le> \<rho>2 \<longleftrightarrow> \<rho>1 = fmap_restr (fdom \<rho>1) \<rho>2"
  unfolding less_eq_fmap_def
  apply transfer
  apply (auto simp add:restrict_map_def split:option.split_asm)
  by (metis option.simps(3))+

lemma fmap_restr_less:
  "fmap_restr S \<rho> \<le> \<rho>"
  unfolding less_eq_fmap_def
  by (transfer, auto)

lemma fmap_upd_less[simp, intro]:
  "\<rho>1 \<le> \<rho>2 \<Longrightarrow> v1 = v2 \<Longrightarrow> \<rho>1(x f\<mapsto> v1) \<le> \<rho>2(x f\<mapsto> v2)"
  apply (rule fmap_less_eqI)
  apply (auto dest: fmap_less_fdom)[1]
  apply (case_tac "xa = x")
  apply (auto dest: fmap_less_eqD)
  done

lemma fmap_update_less[simp, intro]:
  "\<rho>1 \<le> \<rho>1' \<Longrightarrow> \<rho>2 \<le> \<rho>2' \<Longrightarrow>  (fdom \<rho>2' - fdom \<rho>2) \<inter> fdom \<rho>1 = {} \<Longrightarrow> \<rho>1 f++ \<rho>2 \<le> \<rho>1' f++ \<rho>2'"
  apply (rule fmap_less_eqI)
  apply (auto dest: fmap_less_fdom)[1]
  apply (case_tac "x \<in> fdom \<rho>2")
  apply (auto dest: fmap_less_eqD fmap_less_fdom)
  apply (metis fmap_less_eqD fmap_less_fdom lookup_fmap_add1 set_mp)
  by (metis Diff_iff Diff_triv fmap_less_eqD lookup_fmap_add2)

lemma fmap_restr_le:
  assumes "\<rho>1 \<le> \<rho>2"
  assumes "S1 \<subseteq> S2"
  assumes [simp]:"finite S2"
  shows "fmap_restr S1 \<rho>1 \<le> fmap_restr S2 \<rho>2"
proof-
  have [simp]: "finite S1"
    by (rule finite_subset[OF `S1 \<subseteq> S2` `finite S2`])
  show ?thesis
  proof (rule fmap_less_eqI)
    have "fdom \<rho>1 \<subseteq> fdom \<rho>2"
      by (metis assms(1) less_eq_fmap_def)
    thus "fdom (fmap_restr S1 \<rho>1) \<subseteq> fdom (fmap_restr S2 \<rho>2)"
      using `S1 \<subseteq> S2`
      by auto
  next
    fix x
    assume "x \<in> fdom (fmap_restr S1 \<rho>1) "
    hence [simp]:"x \<in> fdom \<rho>1" and [simp]:"x \<in> S1" and [simp]: "x \<in> S2"
      by (auto intro: set_mp[OF `S1 \<subseteq> S2`])
    have "\<rho>1 f! x = \<rho>2 f! x"
      by (metis `x \<in> fdom \<rho>1` assms(1) less_eq_fmap_def)
    thus "(fmap_restr S1 \<rho>1) f! x = (fmap_restr S2 \<rho>2) f! x"
      by simp
  qed
qed
  

end
