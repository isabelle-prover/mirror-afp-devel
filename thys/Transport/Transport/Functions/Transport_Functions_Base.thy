\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport For Functions\<close>
subsection \<open>Basic Setup\<close>
theory Transport_Functions_Base
  imports
    Monotone_Function_Relator
    Transport_Base
begin

paragraph \<open>Summary\<close>
text \<open>Basic setup for closure proofs. We introduce locales for the syntax,
the dependent relator, the non-dependent relator, the monotone dependent relator,
and the monotone non-dependent relator.\<close>


definition "flip2 f x1 x2 x3 x4 \<equiv> f x2 x1 x4 x3"

lemma flip2_eq: "flip2 f x1 x2 x3 x4 = f x2 x1 x4 x3"
  unfolding flip2_def by simp

lemma flip2_eq_rel_inv [simp]: "flip2 R x y = (R y x)\<inverse>"
  by (intro ext) (simp only: flip2_eq rel_inv_iff_rel)

lemma flip2_flip2_eq_self [simp]: "flip2 (flip2 f) = f"
  by (intro ext) (simp add: flip2_eq)

lemma flip2_eq_flip2_iff_eq [iff]: "flip2 f = flip2 g \<longleftrightarrow> f = g"
  unfolding flip2_def by (intro iffI ext) (auto dest: fun_cong)


paragraph \<open>Dependent Function Relator\<close>

locale transport_Dep_Fun_Rel_syntax =
  t1 : transport L1 R1 l1 r1 +
  dfro1 : hom_Dep_Fun_Rel_orders L1 L2 +
  dfro2 : hom_Dep_Fun_Rel_orders R1 R2
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'a2 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b2"
  and r2 :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b1"
begin

notation L1 (infix "\<le>\<^bsub>L1\<^esub>" 50)
notation R1 (infix "\<le>\<^bsub>R1\<^esub>" 50)

notation t1.ge_left (infix "\<ge>\<^bsub>L1\<^esub>" 50)
notation t1.ge_right (infix "\<ge>\<^bsub>R1\<^esub>" 50)

notation t1.left_Galois (infix "\<^bsub>L1\<^esub>\<lessapprox>" 50)
notation t1.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L1\<^esub>" 50)
notation t1.right_Galois (infix "\<^bsub>R1\<^esub>\<lessapprox>" 50)
notation t1.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R1\<^esub>" 50)
notation t1.right_ge_Galois (infix "\<^bsub>R1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_right (infix "\<lessapprox>\<^bsub>R1\<^esub>" 50)
notation t1.left_ge_Galois (infix "\<^bsub>L1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_left (infix "\<lessapprox>\<^bsub>L1\<^esub>" 50)

notation t1.unit ("\<eta>\<^sub>1")
notation t1.counit ("\<epsilon>\<^sub>1")

notation L2 ("(\<le>\<^bsub>L2 (_) (_)\<^esub>)" 50)
notation R2 ("(\<le>\<^bsub>R2 (_) (_)\<^esub>)" 50)

notation dfro1.right_infix ("(_) \<le>\<^bsub>L2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)
notation dfro2.right_infix ("(_) \<le>\<^bsub>R2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)

notation dfro1.o.ge_right ("(\<ge>\<^bsub>L2 (_) (_)\<^esub>)" 50)
notation dfro2.o.ge_right ("(\<ge>\<^bsub>R2 (_) (_)\<^esub>)" 50)

notation dfro1.ge_right_infix ("(_) \<ge>\<^bsub>L2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)
notation dfro2.ge_right_infix ("(_) \<ge>\<^bsub>R2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)

notation l2 ("l2\<^bsub>(_) (_)\<^esub>")
notation r2 ("r2\<^bsub>(_) (_)\<^esub>")

sublocale t2 : transport "(\<le>\<^bsub>L2 x (r1 x')\<^esub>)" "(\<le>\<^bsub>R2 (l1 x) x'\<^esub>)" "l2\<^bsub>x' x\<^esub>" "r2\<^bsub>x x'\<^esub>" for x x' .

notation t2.left_Galois ("(\<^bsub>L2 (_) (_)\<^esub>\<lessapprox>)" 50)
notation t2.right_Galois ("(\<^bsub>R2 (_) (_)\<^esub>\<lessapprox>)" 50)

abbreviation "left2_Galois_infix y x x' y' \<equiv> (\<^bsub>L2 x x'\<^esub>\<lessapprox>) y y'"
notation left2_Galois_infix ("(_) \<^bsub>L2 (_) (_)\<^esub>\<lessapprox> (_)" [51,51,51,51] 50)
abbreviation "right2_Galois_infix y' x x' y \<equiv> (\<^bsub>R2 x x'\<^esub>\<lessapprox>) y' y"
notation right2_Galois_infix ("(_) \<^bsub>R2 (_) (_)\<^esub>\<lessapprox> (_)" [51,51,51,51] 50)

notation t2.ge_Galois_left ("(\<greaterapprox>\<^bsub>L2 (_) (_)\<^esub>)" 50)
notation t2.ge_Galois_right ("(\<greaterapprox>\<^bsub>R2 (_) (_)\<^esub>)" 50)

abbreviation (input) "ge_Galois_left_left2_infix y' x x' y \<equiv> (\<greaterapprox>\<^bsub>L2 x x'\<^esub>) y' y"
notation ge_Galois_left_left2_infix ("(_) \<greaterapprox>\<^bsub>L2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)
abbreviation (input) "ge_Galois_left_right2_infix y x x' y' \<equiv> (\<greaterapprox>\<^bsub>R2 x x'\<^esub>) y y'"
notation ge_Galois_left_right2_infix ("(_) \<greaterapprox>\<^bsub>R2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)

notation t2.right_ge_Galois ("(\<^bsub>R2 (_) (_)\<^esub>\<greaterapprox>)" 50)
notation t2.left_ge_Galois ("(\<^bsub>L2 (_) (_)\<^esub>\<greaterapprox>)" 50)

abbreviation "left2_ge_Galois_left_infix y x x' y' \<equiv> (\<^bsub>L2 x x'\<^esub>\<greaterapprox>) y y'"
notation left2_ge_Galois_left_infix ("(_) \<^bsub>L2 (_) (_)\<^esub>\<greaterapprox> (_)" [51,51,51,51] 50)
abbreviation "right2_ge_Galois_left_infix y' x x' y \<equiv> (\<^bsub>R2 x x'\<^esub>\<greaterapprox>) y' y"
notation right2_ge_Galois_left_infix ("(_) \<^bsub>R2 (_) (_)\<^esub>\<greaterapprox> (_)" [51,51,51,51] 50)

notation t2.Galois_right ("(\<lessapprox>\<^bsub>R2 (_) (_)\<^esub>)" 50)
notation t2.Galois_left ("(\<lessapprox>\<^bsub>L2 (_) (_)\<^esub>)" 50)

abbreviation (input) "Galois_left2_infix y' x x' y \<equiv> (\<lessapprox>\<^bsub>L2 x x'\<^esub>) y' y"
notation Galois_left2_infix ("(_) \<lessapprox>\<^bsub>L2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)
abbreviation (input) "Galois_right2_infix y x x' y' \<equiv> (\<lessapprox>\<^bsub>R2 x x'\<^esub>) y y'"
notation Galois_right2_infix ("(_) \<lessapprox>\<^bsub>R2 (_) (_)\<^esub> (_)" [51,51,51,51] 50)

abbreviation "t2_unit x x' \<equiv> t2.unit x' x"
notation t2_unit ("\<eta>\<^bsub>2 (_) (_)\<^esub>")
abbreviation "t2_counit x x' \<equiv> t2.counit x' x"
notation t2_counit ("\<epsilon>\<^bsub>2 (_) (_)\<^esub>")

end

locale transport_Dep_Fun_Rel =
  transport_Dep_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 l2 r2
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'a2 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b2"
  and r2 :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b1"
begin

definition "L \<equiv> [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>)"

lemma left_rel_eq_Dep_Fun_Rel: "L = ([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 x2\<^esub>))"
  unfolding L_def ..

definition "l \<equiv> ([x' : r1] \<rightarrow> l2 x')"

lemma left_eq_dep_fun_map: "l = ([x' : r1] \<rightarrow> l2 x')"
  unfolding l_def ..

lemma left_eq [simp]: "l f x' = l2\<^bsub>x' (r1 x')\<^esub> (f (r1 x'))"
  unfolding left_eq_dep_fun_map by simp

context
begin

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

abbreviation "R \<equiv> flip.L"
abbreviation "r \<equiv> flip.l"

lemma right_rel_eq_Dep_Fun_Rel: "R = ([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 x1' x2'\<^esub>))"
  unfolding flip.L_def ..

lemma right_eq_dep_fun_map: "r = ([x : l1] \<rightarrow> r2 x)"
  unfolding flip.l_def ..

end

lemma right_eq [simp]: "r g x = r2\<^bsub>x (l1 x)\<^esub> (g (l1 x))"
  unfolding right_eq_dep_fun_map by simp

lemmas transport_defs = left_rel_eq_Dep_Fun_Rel left_eq_dep_fun_map
  right_rel_eq_Dep_Fun_Rel right_eq_dep_fun_map

sublocale transport L R l r .

(*FIXME: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

lemma left_relI [intro]:
  assumes "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> f x1 \<le>\<^bsub>L2 x1 x2\<^esub> f' x2"
  shows "f \<le>\<^bsub>L\<^esub> f'"
  unfolding left_rel_eq_Dep_Fun_Rel using assms by blast

lemma left_relE [elim]:
  assumes "f \<le>\<^bsub>L\<^esub> f'"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  obtains "f x1 \<le>\<^bsub>L2 x1 x2\<^esub> f' x2"
  using assms unfolding left_rel_eq_Dep_Fun_Rel by blast

interpretation flip_inv :
  transport_Dep_Fun_Rel "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 "flip2 R2" "flip2 L2" r2 l2 .

lemma flip_inv_right_eq_ge_left: "flip_inv.R = (\<ge>\<^bsub>L\<^esub>)"
  unfolding left_rel_eq_Dep_Fun_Rel flip_inv.right_rel_eq_Dep_Fun_Rel
  by (simp only: rel_inv_Dep_Fun_Rel_rel_eq flip2_eq_rel_inv[symmetric, of "L2"])

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma flip_inv_left_eq_ge_right: "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)"
  unfolding flip.flip_inv_right_eq_ge_left .


subparagraph \<open>Useful Rewritings for Dependent Relation\<close>

lemma left_rel2_unit_eqs_left_rel2I:
  assumes "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x. x \<le>\<^bsub>L1\<^esub> x \<Longrightarrow> (\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) \<le> (\<le>\<^bsub>L2 x x\<^esub>)"
  and "x \<le>\<^bsub>L1\<^esub> x"
  and "x \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x"
  shows "(\<le>\<^bsub>L2 (\<eta>\<^sub>1 x) x\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
  and "(\<le>\<^bsub>L2 x (\<eta>\<^sub>1 x)\<^esub>) = (\<le>\<^bsub>L2 x x\<^esub>)"
  using assms by (auto intro!: antisym)

lemma left2_eq_if_bi_related_if_monoI:
  assumes mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  and "x1 \<equiv>\<^bsub>L1\<^esub> x3"
  and "x2 \<equiv>\<^bsub>L1\<^esub> x4"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  shows "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x3 x4\<^esub>)"
proof (intro antisym)
  from \<open>x1 \<equiv>\<^bsub>L1\<^esub> x3\<close> \<open>x2 \<equiv>\<^bsub>L1\<^esub> x4\<close> have "x3 \<le>\<^bsub>L1\<^esub> x1" "x2 \<le>\<^bsub>L1\<^esub> x4" by auto
  with \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> mono_L2 show "(\<le>\<^bsub>L2 x1 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x3 x4\<^esub>)" by blast
  from \<open>x1 \<equiv>\<^bsub>L1\<^esub> x3\<close> \<open>x2 \<equiv>\<^bsub>L1\<^esub> x4\<close> have "x1 \<le>\<^bsub>L1\<^esub> x3" "x4 \<le>\<^bsub>L1\<^esub> x2" by auto
  moreover from \<open>x3 \<le>\<^bsub>L1\<^esub> x1\<close> \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> \<open>x2 \<le>\<^bsub>L1\<^esub> x4\<close> have "x3 \<le>\<^bsub>L1\<^esub> x4"
    using trans_L1 by blast
  ultimately show "(\<le>\<^bsub>L2 x3 x4\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" using mono_L2 by blast
qed

end

paragraph \<open>Function Relator\<close>

locale transport_Fun_Rel_syntax =
  tdfrs : transport_Dep_Fun_Rel_syntax L1 R1 l1 r1 "\<lambda>_ _. L2" "\<lambda>_ _. R2"
    "\<lambda>_ _. l2" "\<lambda>_ _. r2"
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'b1 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'b1"
begin

notation L1 (infix "\<le>\<^bsub>L1\<^esub>" 50)
notation R1 (infix "\<le>\<^bsub>R1\<^esub>" 50)

notation tdfrs.t1.ge_left (infix "\<ge>\<^bsub>L1\<^esub>" 50)
notation tdfrs.t1.ge_right (infix "\<ge>\<^bsub>R1\<^esub>" 50)

notation tdfrs.t1.left_Galois (infix "\<^bsub>L1\<^esub>\<lessapprox>" 50)
notation tdfrs.t1.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L1\<^esub>" 50)
notation tdfrs.t1.right_Galois (infix "\<^bsub>R1\<^esub>\<lessapprox>" 50)
notation tdfrs.t1.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R1\<^esub>" 50)
notation tdfrs.t1.right_ge_Galois (infix "\<^bsub>R1\<^esub>\<greaterapprox>" 50)
notation tdfrs.t1.Galois_right (infix "\<lessapprox>\<^bsub>R1\<^esub>" 50)
notation tdfrs.t1.left_ge_Galois (infix "\<^bsub>L1\<^esub>\<greaterapprox>" 50)
notation tdfrs.t1.Galois_left (infix "\<lessapprox>\<^bsub>L1\<^esub>" 50)

notation tdfrs.t1.unit ("\<eta>\<^sub>1")
notation tdfrs.t1.counit ("\<epsilon>\<^sub>1")

notation L2 (infix "\<le>\<^bsub>L2\<^esub>" 50)
notation R2 (infix "\<le>\<^bsub>R2\<^esub>" 50)

notation tdfrs.t2.ge_left (infix "\<ge>\<^bsub>L2\<^esub>" 50)
notation tdfrs.t2.ge_right (infix "\<ge>\<^bsub>R2\<^esub>" 50)

notation tdfrs.t2.left_Galois (infix "\<^bsub>L2\<^esub>\<lessapprox>" 50)
notation tdfrs.t2.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L2\<^esub>" 50)
notation tdfrs.t2.right_Galois (infix "\<^bsub>R2\<^esub>\<lessapprox>" 50)
notation tdfrs.t2.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R2\<^esub>" 50)
notation tdfrs.t2.right_ge_Galois (infix "\<^bsub>R2\<^esub>\<greaterapprox>" 50)
notation tdfrs.t2.Galois_right (infix "\<lessapprox>\<^bsub>R2\<^esub>" 50)
notation tdfrs.t2.left_ge_Galois (infix "\<^bsub>L2\<^esub>\<greaterapprox>" 50)
notation tdfrs.t2.Galois_left (infix "\<lessapprox>\<^bsub>L2\<^esub>" 50)

notation tdfrs.t2.unit ("\<eta>\<^sub>2")
notation tdfrs.t2.counit ("\<epsilon>\<^sub>2")

end

locale transport_Fun_Rel =
  transport_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 l2 r2 +
  tdfr : transport_Dep_Fun_Rel L1 R1 l1 r1 "\<lambda>_ _. L2" "\<lambda>_ _. R2"
    "\<lambda>_ _. l2" "\<lambda>_ _. r2"
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'b1 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'b1"
begin

(*FIXME: we have to repeat the Galois syntax here since tdfr already contains
a Galois instance, blocking a galois sublocale interpretation here*)
notation tdfr.L ("L")
notation tdfr.R ("R")

abbreviation "l \<equiv> tdfr.l"
abbreviation "r \<equiv> tdfr.r"

notation tdfr.L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation tdfr.R (infix "\<le>\<^bsub>R\<^esub>" 50)

notation tdfr.ge_left (infix "\<ge>\<^bsub>L\<^esub>" 50)
notation tdfr.ge_right (infix "\<ge>\<^bsub>R\<^esub>" 50)

notation tdfr.left_Galois (infix "\<^bsub>L\<^esub>\<lessapprox>" 50)
notation tdfr.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L\<^esub>" 50)
notation tdfr.right_Galois (infix "\<^bsub>R\<^esub>\<lessapprox>" 50)
notation tdfr.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R\<^esub>" 50)
notation tdfr.right_ge_Galois (infix "\<^bsub>R\<^esub>\<greaterapprox>" 50)
notation tdfr.Galois_right (infix "\<lessapprox>\<^bsub>R\<^esub>" 50)
notation tdfr.left_ge_Galois (infix "\<^bsub>L\<^esub>\<greaterapprox>" 50)
notation tdfr.Galois_left (infix "\<lessapprox>\<^bsub>L\<^esub>" 50)

notation tdfr.unit ("\<eta>")
notation tdfr.counit ("\<epsilon>")

lemma left_rel_eq_Fun_Rel: "(\<le>\<^bsub>L\<^esub>) = ((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow> (\<le>\<^bsub>L2\<^esub>))"
  unfolding tdfr.left_rel_eq_Dep_Fun_Rel by simp

lemma left_eq_fun_map: "l = (r1 \<rightarrow> l2)"
  by (intro ext) simp

interpretation flip : transport_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma right_rel_eq_Fun_Rel: "(\<le>\<^bsub>R\<^esub>) = ((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow> (\<le>\<^bsub>R2\<^esub>))"
  unfolding flip.left_rel_eq_Fun_Rel ..

lemma right_eq_fun_map: "r = (l1 \<rightarrow> r2)"
  unfolding flip.left_eq_fun_map ..

lemmas transport_defs = left_rel_eq_Fun_Rel right_rel_eq_Fun_Rel
  left_eq_fun_map right_eq_fun_map

end


paragraph \<open>Monotone Dependent Function Relator\<close>

locale transport_Mono_Dep_Fun_Rel =
  transport_Dep_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 l2 r2
  + tdfr : transport_Dep_Fun_Rel L1 R1 l1 r1 L2 R2 l2 r2
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'a2 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b2"
  and r2 :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b1"
begin

definition "L \<equiv> tdfr.L\<^sup>\<oplus>"

lemma left_rel_eq_tdfr_left_Refl_Rel: "L = tdfr.L\<^sup>\<oplus>"
  unfolding L_def ..

lemma left_rel_eq_Mono_Dep_Fun_Rel: "L = ([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>L2 x1 x2\<^esub>))"
  unfolding left_rel_eq_tdfr_left_Refl_Rel tdfr.left_rel_eq_Dep_Fun_Rel by simp

lemma left_rel_eq_tdfr_left_rel_if_reflexive_on:
  assumes "reflexive_on (in_field tdfr.L) tdfr.L"
  shows "L = tdfr.L"
  unfolding left_rel_eq_tdfr_left_Refl_Rel using assms
  by (rule Refl_Rel_eq_self_if_reflexive_on)

abbreviation "l \<equiv> tdfr.l"

lemma left_eq_tdfr_left: "l = tdfr.l" ..

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

abbreviation "R \<equiv> flip.L"

lemma right_rel_eq_tdfr_right_Refl_Rel: "R = tdfr.R\<^sup>\<oplus>"
  unfolding flip.left_rel_eq_tdfr_left_Refl_Rel ..

lemma right_rel_eq_Mono_Dep_Fun_Rel: "R = ([y1 y2 \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<oplus> (\<le>\<^bsub>R2 y1 y2\<^esub>))"
  unfolding flip.left_rel_eq_Mono_Dep_Fun_Rel ..

lemma right_rel_eq_tdfr_right_rel_if_reflexive_on:
  assumes "reflexive_on (in_field tdfr.R) tdfr.R"
  shows "R = tdfr.R"
  using assms by (rule flip.left_rel_eq_tdfr_left_rel_if_reflexive_on)

abbreviation "r \<equiv> tdfr.r"

lemma right_eq_tdfr_right: "r = tdfr.r" ..

lemmas transport_defs = left_rel_eq_tdfr_left_Refl_Rel
  right_rel_eq_tdfr_right_Refl_Rel

sublocale transport L R l r .

(*FIXME: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

end


paragraph \<open>Monotone Function Relator\<close>

locale transport_Mono_Fun_Rel =
  transport_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 l2 r2 +
  tfr : transport_Fun_Rel L1 R1 l1 r1 L2 R2 l2 r2 +
  tpdfr : transport_Mono_Dep_Fun_Rel L1 R1 l1 r1 "\<lambda>_ _. L2" "\<lambda>_ _. R2"
    "\<lambda>_ _. l2" "\<lambda>_ _. r2"
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'b1 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'b1"
begin

(*FIXME: we have to repeat the Galois syntax here since tdfr already contains
a Galois instance, blocking a galois sublocale interpretation here*)
notation tpdfr.L ("L")
notation tpdfr.R ("R")

abbreviation "l \<equiv> tpdfr.l"
abbreviation "r \<equiv> tpdfr.r"

notation tpdfr.L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation tpdfr.R (infix "\<le>\<^bsub>R\<^esub>" 50)

notation tpdfr.ge_left (infix "\<ge>\<^bsub>L\<^esub>" 50)
notation tpdfr.ge_right (infix "\<ge>\<^bsub>R\<^esub>" 50)

notation tpdfr.left_Galois (infix "\<^bsub>L\<^esub>\<lessapprox>" 50)
notation tpdfr.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L\<^esub>" 50)
notation tpdfr.right_Galois (infix "\<^bsub>R\<^esub>\<lessapprox>" 50)
notation tpdfr.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R\<^esub>" 50)
notation tpdfr.right_ge_Galois (infix "\<^bsub>R\<^esub>\<greaterapprox>" 50)
notation tpdfr.Galois_right (infix "\<lessapprox>\<^bsub>R\<^esub>" 50)
notation tpdfr.left_ge_Galois (infix "\<^bsub>L\<^esub>\<greaterapprox>" 50)
notation tpdfr.Galois_left (infix "\<lessapprox>\<^bsub>L\<^esub>" 50)

notation tpdfr.unit ("\<eta>")
notation tpdfr.counit ("\<epsilon>")

lemma left_rel_eq_Mono_Fun_Rel: "(\<le>\<^bsub>L\<^esub>) = ((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<oplus> (\<le>\<^bsub>L2\<^esub>))"
  unfolding tpdfr.left_rel_eq_Mono_Dep_Fun_Rel by simp

lemma left_eq_fun_map: "l = (r1 \<rightarrow> l2)"
  unfolding tfr.left_eq_fun_map ..

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

lemma right_rel_eq_Mono_Fun_Rel: "(\<le>\<^bsub>R\<^esub>) = ((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<oplus> (\<le>\<^bsub>R2\<^esub>))"
  unfolding flip.left_rel_eq_Mono_Fun_Rel ..

lemma right_eq_fun_map: "r = (l1 \<rightarrow> r2)"
  unfolding flip.left_eq_fun_map ..

lemmas transport_defs = tpdfr.transport_defs

end


end