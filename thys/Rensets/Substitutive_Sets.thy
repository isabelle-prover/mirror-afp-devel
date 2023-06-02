section \<open>Substitutive Sets\<close>

theory Substitutive_Sets
  imports FRBCE_Rensets
begin

text \<open>This theory describes a variation of the renset algebraic theory, including 
initiality and recursion principle, but focusing on term-for-variable rather than 
variable-for-variable substitution. Instead of rensets, we work with what we call 
substitutive sets.\<close>

subsection \<open>Substitutive Sets\<close>

locale Substitutive_Set = 
  fixes substA :: "'A \<Rightarrow> 'A \<Rightarrow> var \<Rightarrow> 'A"
    and VrA :: "var \<Rightarrow> 'A"
  assumes substA_id[simp]: "\<And>x a. substA a (VrA x) x = a"
    and substA_idem: "\<And>x b1 b2 a.  u \<noteq> x \<Longrightarrow> 
  let b1' = substA b1 (VrA u) x in substA (substA a b1' x) b2 x = substA a b1' x"
    and 
    substA_chain: "\<And> u x1 x2 b3 a. u \<noteq> x2 \<Longrightarrow> 
  substA (substA (substA a (VrA u) x2) (VrA x2) x1) b3 x2 = 
  substA (substA a (VrA u) x2) b3 x1"
    and 
    substA_commute_diff: 
    "\<And> x y a e f. x \<noteq> y \<Longrightarrow> u \<noteq> y \<Longrightarrow> v \<noteq> x \<Longrightarrow> 
let e' = substA e (VrA u) y; f' = substA f (VrA v) x in
substA (substA a e' x) f' y = substA (substA a f' y) e' x"
    and 
    substA_VrA: "\<And> x a z. substA (VrA x) a z = (if x = z then a else VrA x)"
begin 


lemma substA_idem_var[simp]: 
  "y1 \<noteq> x \<Longrightarrow> substA (substA a (VrA y1) x) (VrA y2) x = substA a (VrA y1) x"
  by (metis substA_VrA substA_idem)

lemma substA_commute_diff_var: 
  "x \<noteq> v \<Longrightarrow> y \<noteq> u \<Longrightarrow> x \<noteq> y \<Longrightarrow> 
substA (substA a (VrA u) x) (VrA v) y = substA (substA a (VrA v) y) (VrA u) x"
  by (metis substA_VrA substA_commute_diff) 

end (* context Substitutive_Set *)


text \<open>Any substitutive set is in particular a renset:\<close>

sublocale Substitutive_Set < Renset where 
  "vsubstA" = "\<lambda>a x. substA a (VrA x)" apply standard 
  using substA_chain substA_commute_diff_var substA_VrA by auto

(* Terms with strong substitution form a strongly substitutive set: *)
interpretation STerm: Substitutive_Set where substA = subst and VrA = Vr
  unfolding Substitutive_Set_def
	using fresh_subst_same subst_chain fresh_subst
	using fresh_subst_id subst_comp_diff by auto


subsection \<open>Constructor-Enriched (CE) Substitutive Sets\<close>

locale CE_Substitutive_Set = Substitutive_Set substA VrA 
  for substA :: "'A \<Rightarrow> 'A \<Rightarrow> var \<Rightarrow> 'A" and VrA
    +
  fixes 
    X :: "'A set"
    and
    (* Constructor-like operators (VrA already exists): *)
    ApA :: "'A \<Rightarrow> 'A \<Rightarrow> 'A"
    and LmA :: "var \<Rightarrow> 'A \<Rightarrow> 'A"
  assumes  
    substA_ApA: "\<And> y z a1 a2. 
  substA (ApA a1 a2) y z =  
  ApA (substA a1 y z) 
      (substA a2 y z)"
    and 
    substA_LmA: "\<And> a z x e u. 
  let e' = substA e (VrA u) x in 
  substA (LmA x a) e' z = (if x = z then LmA x a else LmA x (substA a e' z))"
    and 
    LmA_rename: "\<And> x y z a.  
  z \<noteq> y \<Longrightarrow> LmA x (substA a (VrA z) y) = LmA y (substA (substA a (VrA z) y) (VrA y) x)"
begin 

lemma LmA_cong: "\<And> z x x' a a' u.   
 z \<noteq> u \<Longrightarrow> 
 z \<noteq> x \<Longrightarrow> z \<noteq> x' \<Longrightarrow> 
 substA (substA a (VrA u) z) (VrA z) x = substA (substA a' (VrA u) z) (VrA z) x'
 \<Longrightarrow> LmA x (substA a (VrA u) z) = LmA x' (substA a' (VrA u) z)"
	by (metis LmA_rename)

lemma substA_LmA_same: 
  "substA (LmA x a) e x = LmA x a" 
  by (metis vsubstA_id substA_LmA)  

lemma substA_LmA_diff: 
  "freshA x e \<Longrightarrow> x \<noteq> z \<Longrightarrow> substA (LmA x a) e z = LmA x (substA a e z)"
  using vsubstA_id by (metis substA_LmA)

lemma freshA_2_substA: 
  assumes "freshA z a" "freshA z a'" 
  shows "\<exists>u. u \<noteq> z \<and> substA a (VrA u) z = a \<and> substA a' (VrA u) z = a'"
  using assms unfolding freshA_def by (meson assms(1) assms(2) local.freshA_iff_all_vvsubstA_idle freshA_iff_ex_vvsubstA_idle)

lemma LmA_cong_freshA:  
  assumes "freshA z a" "freshA z a'" "substA a (VrA z) x = substA a' (VrA z) x'"
  shows "LmA x a = LmA x' a'"
  by (metis LmA_rename assms freshA_2_substA) 

lemma freshA_VrA: "z \<noteq> x \<Longrightarrow> freshA z (VrA x)"
  using freshA_def substA_VrA by auto

lemma freshA_ApA: "\<And> z a1 a2. freshA z a1 \<Longrightarrow> freshA z a2 \<Longrightarrow> freshA z (ApA a1 a2)"
  by (simp add: freshA_iff_all_vvsubstA_idle substA_ApA)

lemma freshA_LmA_same: 
  "freshA x (LmA x a)"
  using freshA_iff_all_vvsubstA_idle substA_LmA_same by presburger

lemma freshA_LmA: 
  assumes "freshA z a"  
  shows "freshA z (LmA x a)"
  by (metis LmA_rename assms freshA_2_substA freshA_iff_all_vvsubstA_idle substA_LmA_same)

end (* contex CE_Substitutive_Set *)


text \<open>Any CE substitutive set is in particular a CE renset:\<close>

sublocale CE_Substitutive_Set < CE_Renset 
  where vsubstA = "\<lambda>a x. substA a (VrA x)"
  by (simp add: CE_Renset_axioms_def CE_Renset_def LmA_rename Renset_axioms freshA_VrA substA_ApA substA_LmA_diff substA_LmA_same substA_VrA)

subsection \<open>The recursion theorem for substitutive sets\<close>

context CE_Substitutive_Set 
begin

(* We borrow all these theorems from CE_Renset : *) 
lemmas f_clauses' = f_Vr f_Ap f_Lm f_fresh f_subst f_unique
  (* and can further prove: *)

theorem f_subst_strong: 
  "f (subst t s z) = substA (f t) (f s) z"
proof-
  have "finite ({z} \<union> FFvars s)"   
  	by (simp add: cofinite_fresh)
  thus ?thesis 
  proof(induct t rule: fresh_induct)
    case (Vr x)
    then show ?case
      by (simp add: substA_VrA)
  next
    case (Ap t1 t2)
    then show ?case
      using substA_ApA by force
  next
    case (Lm x t)
    then show ?case
      by (simp add: f_fresh substA_LmA_diff)
  qed 
qed

end (* CE_Substitutive_Set *)


end 