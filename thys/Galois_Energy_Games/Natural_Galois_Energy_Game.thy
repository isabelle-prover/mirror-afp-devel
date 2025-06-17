section \<open>Galois Energy Games over Naturals\<close>

theory Natural_Galois_Energy_Game
  imports Energy_Game Energy_Order Decidability Update
begin

text\<open>We now define Galois energy games over vectors of naturals with the component-wise order. 
We formalise this in this theory as an \<open>energy_game\<close> with a fixed dimension. In particular, we assume all updates to have an upward-closed domain (as \<open>domain_upw_closed\<close>) and be length-preserving (as \<open>upd_preserves_length\<close>). 
We assume the latter for the inversion of updates too (as \<open>inv_preserves_length\<close>) and assume that the inversion of an update is a total mapping from energies to the domain of the update (as \<open>domain_inv\<close>). 
(This corresponds to section 4.2 in the preprint~\cite{preprint}.)\<close>

locale natural_galois_energy_game = energy_game attacker weight application
  for   attacker ::  "'position set" and 
        weight :: "'position \<Rightarrow> 'position \<Rightarrow> 'label option" and
        application :: "'label \<Rightarrow> energy \<Rightarrow> energy option" and
        inverse_application :: "'label \<Rightarrow> energy \<Rightarrow> energy option"
+ 
  fixes dimension :: "nat"
  assumes
    domain_upw_closed: "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> e e\<le> e' \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> application (the (weight p p')) e' \<noteq> None"
    and updgalois: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> length (the (application (the (weight p p')) e)) = length e"
    and inv_preserves_length: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> length e = dimension \<Longrightarrow> length (the (inverse_application (the (weight p p')) e)) = length e"
    and domain_inv: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> length e = dimension \<Longrightarrow> (inverse_application (the (weight p p')) e) \<noteq> None \<and> application (the (weight p p')) (the (inverse_application (the (weight p p')) e)) \<noteq> None"
    and galois: "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> application (the (weight p p')) e' \<noteq> None \<Longrightarrow> length e = dimension \<Longrightarrow> length e' = dimension \<Longrightarrow> (the (inverse_application (the (weight p p')) e)) e\<le> e' = e e\<le> (the (application (the (weight p p')) e'))"

sublocale natural_galois_energy_game \<subseteq> galois_energy_game attacker weight application inverse_application "{e::energy. length e = dimension}" energy_leq "\<lambda>s. energy_sup dimension s"
proof
  show "wqo_on energy_leq {e::energy. length e = dimension}" 
    using Energy_Order.energy_leq_wqo . 

  show "\<And> set s'. set \<subseteq> {e::energy. length e = dimension} \<Longrightarrow> finite set \<Longrightarrow> energy_sup dimension set \<in> {e::energy. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> energy_leq s (energy_sup dimension set)) \<and> (s' \<in> {e::energy. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> energy_leq s s') \<longrightarrow> energy_leq (energy_sup dimension set) s')"
  proof-
    fix set
    show "\<And>s'. set \<subseteq> {e::energy. length e = dimension} \<Longrightarrow> finite set \<Longrightarrow> energy_sup dimension set \<in> {e::energy. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> energy_leq s (energy_sup dimension set)) \<and> (s' \<in> {e::energy. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> energy_leq s s') \<longrightarrow> energy_leq (energy_sup dimension set) s')"
    proof
      fix s'
      assume "set \<subseteq> {e. length e = dimension}" and "finite set"
      show "energy_sup dimension set \<in> {e. length e = dimension}"
        unfolding energy_sup_def
        by simp 
      show "(\<forall>s. s \<in> set \<longrightarrow> energy_leq s (energy_sup dimension set)) \<and> (s' \<in> {e::energy. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> energy_leq s s') \<longrightarrow> energy_leq (energy_sup dimension set) s')"
      proof
        show "(\<forall>s. s \<in> set \<longrightarrow> s e\<le> energy_sup dimension set)"
          using energy_sup_is_sup(1) \<open>set \<subseteq> {e. length e = dimension}\<close>
          by auto
        show "s' \<in> {e. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> s e\<le> s') \<longrightarrow> energy_sup dimension set e\<le> s' "
        proof
          assume "s' \<in> {e. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> s e\<le> s')"
          show "energy_sup dimension set e\<le> s'"
          proof(rule energy_sup_is_sup(2))
            show "\<And>a. a \<in> set \<Longrightarrow> a e\<le> s'"
              by (simp add: \<open>s' \<in> {e. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> s e\<le> s')\<close>) 
            show "length s' = dimension"
              using \<open>s' \<in> {e. length e = dimension} \<and> (\<forall>s. s \<in> set \<longrightarrow> s e\<le> s')\<close> by auto
          qed
        qed
      qed
    qed
  qed

  show "\<And>e e'. e \<in> {e::energy. length e = dimension} \<Longrightarrow> e e\<le> e' \<Longrightarrow> e' \<in> {e::energy. length e = dimension}"
    unfolding Energy_Order.energy_leq_def by simp

  show "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> e \<in> {e::energy. length e = dimension} \<Longrightarrow> (the (application (the (weight p p')) e)) \<in> {e::energy. length e = dimension}"
    using inv_preserves_length
    by (simp add: updgalois) 

  show  "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e \<in> {e::energy. length e = dimension} \<Longrightarrow> (inverse_application (the (weight p p')) e) \<noteq> None \<and> (the (inverse_application (the (weight p p')) e)) \<in> {e::energy. length e = dimension} \<and> application (the (weight p p')) (the (inverse_application (the (weight p p')) e)) \<noteq> None" 
    using inv_preserves_length domain_inv by simp

  show "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> energy_leq e e' \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> application (the (weight p p')) e' \<noteq> None"
    using local.domain_upw_closed .

  show  "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> application (the (weight p p')) e' \<noteq> None \<Longrightarrow> e \<in> {e::energy. length e = dimension} \<Longrightarrow> e' \<in> {e::energy. length e = dimension} \<Longrightarrow> energy_leq (the (inverse_application (the (weight p p')) e)) e' = energy_leq e (the (application (the (weight p p')) e'))"
    using galois by simp
qed

locale natural_galois_energy_game_decidable = natural_galois_energy_game attacker weight application inverse_application dimension
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> 'label option" and
      application :: "'label \<Rightarrow> energy \<Rightarrow> energy option" and
      inverse_application :: "'label \<Rightarrow> energy \<Rightarrow> energy option" and
      dimension :: "nat"
+
assumes nonpos_eq_pos: "nonpos_winning_budget = winning_budget" and
        finite_positions: "finite positions"
                                 
sublocale natural_galois_energy_game_decidable \<subseteq> galois_energy_game_decidable attacker weight application inverse_application "{e::energy. length e = dimension}" energy_leq "\<lambda>s. energy_sup dimension s"
proof
  show "nonpos_winning_budget = winning_budget" and "finite positions" using nonpos_eq_pos finite_positions by auto
qed

text\<open>Bisping's only considers declining energy games over vectors of naturals. We generalise this by considering all valid updates. 
We formalise this in this theory as an \<open>energy_game\<close> with a fixed dimension and show that such games are Galois energy games. \<close>

locale bispings_energy_game = energy_game attacker weight apply_update 
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> update option"
+ 
  fixes dimension :: "nat"
  assumes
    valid_updates: "\<forall>p. \<forall>p'. ((weight p p' \<noteq> None ) 
                    \<longrightarrow> ((length (the (weight p p')) = dimension) 
                    \<and> valid_update (the (weight p p'))))"

sublocale bispings_energy_game \<subseteq> natural_galois_energy_game attacker weight apply_update apply_inv_update dimension
proof
  show "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> e e\<le> e' \<Longrightarrow> apply_w p p' e \<noteq> None \<Longrightarrow> apply_w p p' e' \<noteq> None"
    using upd_domain_upward_closed
    by blast
  show "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> apply_w p p' e \<noteq> None \<Longrightarrow> length (upd (the (weight p p')) e) = length e"
    using len_appl
    by simp
  show "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> length e = dimension \<Longrightarrow> length (inv_upd (the (weight p p')) e) = length e"
    using len_inv_appl valid_updates
    by blast
  show "\<And>p p' e.
       weight p p' \<noteq> None \<Longrightarrow>
       length e = dimension \<Longrightarrow>
       apply_inv_update (the (weight p p')) e \<noteq> None \<and> apply_w p p' (inv_upd (the (weight p p')) e) \<noteq> None"
    using  inv_not_none  inv_not_none_then
    using valid_updates by presburger
  show "\<And>p p' e e'.
       weight p p' \<noteq> None \<Longrightarrow>
       apply_w p p' e' \<noteq> None \<Longrightarrow>
       length e = dimension \<Longrightarrow>
       length e' = dimension \<Longrightarrow> inv_upd (the (weight p p')) e e\<le> e' = e e\<le> upd (the (weight p p')) e'"
    using galois_connection
    by (metis valid_updates) 
qed

locale bispings_energy_game_decidable = bispings_energy_game attacker weight dimension
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> update option" and 
      dimension :: "nat"
+
assumes nonpos_eq_pos: "nonpos_winning_budget = winning_budget" and
        finite_positions: "finite positions"

sublocale bispings_energy_game_decidable \<subseteq> natural_galois_energy_game_decidable attacker weight apply_update apply_inv_update dimension
proof
  show "nonpos_winning_budget = winning_budget" using nonpos_eq_pos.
  show "finite positions" using finite_positions .
qed

end