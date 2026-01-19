\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport for Dependent Function Relator with Non-Dependent Functions\<close>
theory Transport_No_Dep_Fun
  imports
    Transport_Functions
begin

section \<open>Transport for Dependent Function Relator with Non-Dependent Functions\<close>
paragraph \<open>Summary\<close>
text \<open>We introduce a special case of @{locale transport_Dep_Fun_Rel}.
The derived theorem is easier to apply and supported by the current prototype.\<close>

locale transport_Dep_Fun_Rel_no_dep_fun =
  transport_Dep_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 "\<lambda>_ _. l2" "\<lambda>_ _. r2" +
  tdfr : transport_Dep_Fun_Rel L1 R1 l1 r1 L2 R2 "\<lambda>_ _. l2" "\<lambda>_ _. r2"
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'b1 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'b1"
begin

notation t2.unit (\<open>\<eta>\<^sub>2\<close>)
notation t2.counit (\<open>\<epsilon>\<^sub>2\<close>)

abbreviation "L \<equiv> tdfr.L"
abbreviation "R \<equiv> tdfr.R"

abbreviation "l \<equiv> tdfr.l"
abbreviation "r \<equiv> tdfr.r"

notation tdfr.L (infix \<open>\<le>\<^bsub>L\<^esub>\<close> 50)
notation tdfr.R (infix \<open>\<le>\<^bsub>R\<^esub>\<close> 50)

notation tdfr.ge_left (infix \<open>\<ge>\<^bsub>L\<^esub>\<close> 50)
notation tdfr.ge_right (infix \<open>\<ge>\<^bsub>R\<^esub>\<close> 50)

notation tdfr.unit (\<open>\<eta>\<close>)
notation tdfr.counit (\<open>\<epsilon>\<close>)

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2 r2"
  and tdfr.mono_conds_rel
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from assms have per2I: "((\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2 r2"
    if "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<^bsub>L1\<^esub>\<lessapprox> x1'" "x1' \<le>\<^bsub>R1\<^esub> x2'" for x1 x2 x1' x2'
    using that t1.left_Galois_if_left_Galois_if_left_relI
      t1.left_Galois_if_right_rel_if_left_GaloisI
    by fastforce
  have "tdfr.mono_conds_fun"
    by (intro tdfr.mono_conds_funI tdfr.mono_cond_left_funI tdfr.mono_cond_right_funI dep_mono_wrt_relI
      Dep_Fun_Rel_relI Dep_Fun_Rel_predI)
    (auto 0 10 dest!: per2I)
  with assms show ?thesis by (intro tdfr.partial_equivalence_rel_equivalenceI) auto
qed

end

end