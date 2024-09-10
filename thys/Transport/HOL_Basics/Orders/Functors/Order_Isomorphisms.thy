\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofa"\<close>
theory Order_Isomorphisms
  imports
    Transport_Bijections
begin

consts order_isomorphism_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> bool"

definition order_isomorphism_on_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow>
  ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "order_isomorphism_on_pred P Q L R l r \<equiv> bijection_on P Q l r \<and> (\<forall>x y : P. L x y \<longleftrightarrow> R (l x) (l y))"
adhoc_overloading order_isomorphism_on order_isomorphism_on_pred

context order_functors
begin

lemma order_isomorphism_onI [intro]:
  assumes bij: "bijection_on P Q l r"
  and monol: "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l"
  and monor: "((\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub> \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r"
  shows "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
proof -
  have "x \<le>\<^bsub>L\<^esub> x'" if "P x" "P x'" "l x \<le>\<^bsub>R\<^esub> l x'" for x x'
  proof -
    have "\<eta> x \<le>\<^bsub>L\<^esub> \<eta> x'" using that monor bij by fastforce
    then show ?thesis
      using \<open>P x\<close> \<open>P x'\<close> bij inverse_on_if_bijection_on_left_right by (force dest: inverse_onD)
  qed
  then have "x \<le>\<^bsub>L\<^esub> x' \<longleftrightarrow> l x \<le>\<^bsub>R\<^esub> l x'" if "P x" "P x'" for x x' using that monol by fast
  then show ?thesis unfolding order_isomorphism_on_pred_def using bij by auto
qed

lemma order_isomorphism_onE:
  assumes "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  obtains "bijection_on P Q l r" "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> L x y \<longleftrightarrow> R (l x) (l y)"
  using assms unfolding order_isomorphism_on_pred_def by auto

context
  notes order_isomorphism_onE[elim!]
begin

lemma right_rel_right_if_right_rel_if_preds_if_order_isomorphism_on:
  assumes "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  and "Q y" "Q y'"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "r y \<le>\<^bsub>L\<^esub> r y'"
proof -
  from assms have "y = \<epsilon> y" "y' = \<epsilon> y'"
    using inverse_on_if_bijection_on_left_right inverse_on_if_bijection_on_right_left
    by (force dest!: inverse_onD)+
  with assms show ?thesis by force
qed

lemma order_isomorphism_on_right_left_if_order_isomorphism_on_left_right:
  assumes "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  shows "order_isomorphism_on Q P (\<le>\<^bsub>R\<^esub>) (\<le>\<^bsub>L\<^esub>) r l"
  using assms bijection_on_right_left_if_bijection_on_left_right[of P Q l r]
    right_rel_right_if_right_rel_if_preds_if_order_isomorphism_on[OF assms]
  by (intro order_functors.order_isomorphism_onI mono_wrt_relI)
  (auto elim!: order_isomorphism_onE rel_restrict_leftE rel_restrict_rightE)

lemma mono_wrt_restrict_restrict_left_if_order_isomorphism_on:
  assumes "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<Rightarrow> (\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub>) l"
  using assms unfolding order_isomorphism_on_pred_def by fastforce

end
end

context galois
begin

interpretation flip : galois R L r l .

lemma order_isomorphism_onE [elim]:
  assumes "order_isomorphism_on P Q (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  obtains "bijection_on P Q l r" "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub>) l r"
proof -
  note order_isomorphism_onE[elim]
  have "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<Rightarrow> (\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub>) l"
    using assms by (intro mono_wrt_restrict_restrict_left_if_order_isomorphism_on)
  moreover have "((\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub> \<Rightarrow> (\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub>) r"
    using assms by (intro flip.mono_wrt_restrict_restrict_left_if_order_isomorphism_on
      order_isomorphism_on_right_left_if_order_isomorphism_on_left_right)
  moreover have "inverse_on (in_field (\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub>) l r"
  proof -
    have "in_field (\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<le> P" by auto
    with assms show ?thesis using antimono_inverse_on by blast
  qed
  moreover have "inverse_on (in_field (\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub>) r l"
  proof -
    have "in_field (\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub> \<le> Q" by auto
    with assms show ?thesis using antimono_inverse_on by blast
  qed
  ultimately interpret transport_bijection "(\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub>" "(\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>Q\<^esub>" l r
    using assms unfolding order_isomorphism_on_pred_def by unfold_locales auto
  from assms galois_equivalence show ?thesis using that by blast
qed

lemma order_isomorphism_on_in_field_if_connected_on_if_asymmetric_if_galois_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "asymmetric (\<le>\<^bsub>L\<^esub>)" "asymmetric (\<le>\<^bsub>R\<^esub>)"
  and "connected_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)" "connected_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "order_isomorphism_on (in_field (\<le>\<^bsub>L\<^esub>)) (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>L\<^esub>) (\<le>\<^bsub>R\<^esub>) l r"
  using assms by (intro order_isomorphism_onI
    bijection_on_if_connected_on_if_asymmetric_if_galois_equivalence)
  blast+

end

context order_functors
begin

interpretation of : order_functors A B a b for A B a b .

lemma order_isomorphism_on_compI:
  assumes "order_isomorphism_on P Q L M l1 r1"
  and "order_isomorphism_on Q U M R l2 r2"
  shows "order_isomorphism_on P U L R (l2 \<circ> l1) (r1 \<circ> r2)"
proof (intro of.order_isomorphism_onI)
  from assms show "bijection_on P U (l2 \<circ> l1) (r1 \<circ> r2)"
    by (intro bijection_on_compI) (auto elim: of.order_isomorphism_onE)
  from assms show "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) (l2 \<circ> l1)"
  proof -
    from assms have "((\<le>\<^bsub>L\<^esub>)\<up>\<^bsub>P\<^esub> \<Rightarrow> M\<up>\<^bsub>Q\<^esub>) l1" "(M\<up>\<^bsub>Q\<^esub> \<Rightarrow> (\<le>\<^bsub>R\<^esub>)) l2"
      using of.mono_wrt_restrict_restrict_left_if_order_isomorphism_on by blast+
    then show ?thesis by (urule dep_mono_wrt_rel_compI')
  qed
  from assms show "((\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>U\<^esub> \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) (r1 \<circ> r2)"
  proof -
    from assms have "order_isomorphism_on Q P M L r1 l1" "order_isomorphism_on U Q R M r2 l2"
      by (auto intro: of.order_isomorphism_on_right_left_if_order_isomorphism_on_left_right)
    then have "((\<le>\<^bsub>R\<^esub>)\<up>\<^bsub>U\<^esub> \<Rightarrow> M\<up>\<^bsub>Q\<^esub>) r2" "(M\<up>\<^bsub>Q\<^esub> \<Rightarrow> (\<le>\<^bsub>L\<^esub>)) r1"
      using of.mono_wrt_restrict_restrict_left_if_order_isomorphism_on by blast+
    then show ?thesis by (urule dep_mono_wrt_rel_compI')
  qed
qed

lemma order_isomorphism_on_self_id: "order_isomorphism_on P P R R id id"
  by (intro of.order_isomorphism_onI bijection_on_self_id) fastforce+

end

consts order_isomorphic_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"

definition order_isomorphic_on_pred ::
  "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "order_isomorphic_on_pred P Q L R \<equiv> \<exists>l r. order_isomorphism_on P Q L R l r"
adhoc_overloading order_isomorphic_on order_isomorphic_on_pred

lemma order_isomorphic_onI [intro]:
  assumes "order_isomorphism_on P Q L R l r"
  shows "order_isomorphic_on P Q L R"
  using assms unfolding order_isomorphic_on_pred_def by blast

lemma order_isomorphic_onE [elim]:
  assumes "order_isomorphic_on P Q L R"
  obtains l r where "order_isomorphism_on P Q L R l r"
  using assms unfolding order_isomorphic_on_pred_def by blast

lemma order_isomorphic_on_if_order_isomorphic_on:
  assumes "order_isomorphic_on P Q L R"
  shows "order_isomorphic_on Q P R L"
  using assms order_functors.order_isomorphism_on_right_left_if_order_isomorphism_on_left_right
  by blast

lemma order_isomorphic_on_trans:
  assumes "order_isomorphic_on P Q L M"
  and "order_isomorphic_on Q U M R"
  shows "order_isomorphic_on P U L R"
  using assms by (elim order_isomorphic_onE) (blast intro: order_functors.order_isomorphism_on_compI)

lemma order_isomorphic_on_self: "order_isomorphic_on P P R R"
  using order_functors.order_isomorphism_on_self_id by blast

end