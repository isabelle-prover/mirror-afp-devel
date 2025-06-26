section \<open>Galois Energy Games\<close>

theory Galois_Energy_Game
  imports Energy_Game Well_Quasi_Orders.Well_Quasi_Orders
begin

text\<open>We now define Galois energy games over well-founded bounded join-semilattices.
We do this by building on a previously defined \<open>energy_game\<close>.
In particular, we add a set of energies \<open>energies\<close> with an order \<open>order\<close> and a supremum mapping \<open>energy_sup\<close>.
Then, we assume the set to be partially ordered in \<open>energy_order\<close>, the order to be well-founded in \<open>energy_wqo\<close>, 
the supremum to map finite sets to the least upper bound \<open>bounded_join_semilattice\<close> and the set to be upward-closed w.r.t\ the order in \<open>upward_closed_energies\<close>. 
Further, we assume the updates to actually map energies (elements of the set \<open>enegies\<close>) to energies with \<open>upd_well_defined\<close>
and assume the inversion to map updates to total functions between the set of energies and the domain of the update in \<open>inv_well_defined\<close>.
The latter is assumed to be upward-closed in \<open>domain_upw_closed\<close>.
Finally, we assume the updates to be Galois-connected with their inverse in \<open>galois\<close>. 
(This corresponds to section 2.3 in the preprint~\cite{preprint}.)
 \<close>

locale galois_energy_game = energy_game attacker weight application
  for   attacker ::  "'position set" and 
        weight :: "'position \<Rightarrow> 'position \<Rightarrow> 'label option" and
        application :: "'label \<Rightarrow> 'energy \<Rightarrow> 'energy option" and
        inverse_application :: "'label \<Rightarrow> 'energy \<Rightarrow> 'energy option"
+ 
  fixes energies :: "'energy set" and
        order :: "'energy \<Rightarrow> 'energy \<Rightarrow> bool" (infix "e\<le>" 80)and 
        energy_sup :: "'energy set \<Rightarrow> 'energy"
      assumes 
        energy_order: "ordering order (\<lambda>e e'. order e e' \<and> e \<noteq> e')" and 
        energy_wqo: "wqo_on order energies" and 
        bounded_join_semilattice: "\<And> set s'. set \<subseteq> energies \<Longrightarrow> finite set 
        \<Longrightarrow> energy_sup set \<in> energies 
            \<and> (\<forall>s. s \<in> set \<longrightarrow> order s (energy_sup set)) 
            \<and> (s' \<in> energies \<and> (\<forall>s. s \<in> set \<longrightarrow> order s s') \<longrightarrow> order (energy_sup set) s')" and
        upward_closed_energies: "\<And>e e'. e \<in> energies \<Longrightarrow> e e\<le> e' \<Longrightarrow> e' \<in> energies" and
        upd_well_defined: "\<And>p p' e. weight p p' \<noteq> None 
        \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> e \<in> energies 
        \<Longrightarrow> (the (application (the (weight p p')) e)) \<in> energies" and
        inv_well_defined: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e \<in> energies 
        \<Longrightarrow> (inverse_application (the (weight p p')) e) \<noteq> None 
        \<and> (the (inverse_application (the (weight p p')) e)) \<in> energies 
        \<and> application (the (weight p p')) (the (inverse_application (the (weight p p')) e)) \<noteq> None" and        
        domain_upw_closed: "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> order e e' 
        \<Longrightarrow> application (the (weight p p')) e \<noteq> None 
        \<Longrightarrow> application (the (weight p p')) e' \<noteq> None" and
        galois: "\<And>p p' e e'. weight p p' \<noteq> None 
        \<Longrightarrow> application (the (weight p p')) e' \<noteq> None 
        \<Longrightarrow> e \<in> energies \<Longrightarrow> e' \<in> energies 
        \<Longrightarrow> order (the (inverse_application (the (weight p p')) e)) e' = order e (the (application (the (weight p p')) e'))"
begin

abbreviation "upd u e \<equiv> the (application u e)"
abbreviation "inv_upd u e \<equiv> the (inverse_application u e)"

abbreviation energy_l:: "'energy \<Rightarrow> 'energy \<Rightarrow> bool" (infix "e<" 80) where 
  "energy_l e e' \<equiv>  e e\<le> e' \<and> e \<noteq> e'"

subsection\<open>Properties of Galois connections\<close>
text\<open>The following properties are described by Erné et al.~\cite{galois}. \<close>


lemma galois_properties: 
  shows upd_inv_increasing: 
   "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies 
    \<Longrightarrow> order e (the (application (the (weight p p')) (the (inverse_application (the (weight p p')) e))))"
   and inv_upd_decreasing: 
  "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies 
  \<Longrightarrow> application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the (inverse_application (the (weight p p')) (the (application (the (weight p p')) e))) e\<le> e"
  and updates_monotonic: 
  "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow>e\<in>energies \<Longrightarrow> e e\<le> e' 
  \<Longrightarrow> application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the( application (the (weight p p')) e) e\<le> the (application (the (weight p p')) e')"
  and inverse_monotonic: 
  "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies \<Longrightarrow> e e\<le> e' 
  \<Longrightarrow> inverse_application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the( inverse_application (the (weight p p')) e) e\<le> the (inverse_application (the (weight p p')) e')"
proof-
  show upd_inv_increasing: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies 
    \<Longrightarrow> order e (the (application (the (weight p p')) (the (inverse_application (the (weight p p')) e))))"
  proof-
    fix p p' e 
    assume "weight p p' \<noteq> None" 
    define u where "u= the (weight p p')"
    show "e\<in>energies  \<Longrightarrow> order e (the (application (the (weight p p')) (the (inverse_application (the (weight p p')) e))))"
    proof-
      assume "e\<in>energies"
      have "order (inv_upd u e) (inv_upd u e)"
        by (meson local.energy_order ordering.eq_iff)

      define e' where "e' = inv_upd u e"
      have "(inv_upd u e e\<le> e') = e e\<le> upd u e'"
        unfolding u_def using \<open>weight p p' \<noteq> None\<close> proof(rule galois)
        show "apply_w p p' e' \<noteq> None"
          using \<open>e\<in>energies\<close> \<open>weight p p' \<noteq> None\<close> e'_def inv_well_defined u_def by presburger
        show "e\<in>energies" using \<open>e\<in>energies\<close>.
        show "e'\<in>energies" unfolding e'_def
          using \<open>e\<in>energies\<close> \<open>weight p p' \<noteq> None\<close> inv_well_defined u_def
          by blast
      qed   
      hence "e e\<le> upd u (inv_upd u e)"
        using  \<open>inv_upd u e e\<le> inv_upd u e\<close> e'_def by auto
      thus "order e (the (application (the (weight p p')) (the (inverse_application (the (weight p p')) e))))"
        using u_def by auto
    qed
  qed

  show inv_upd_decreasing: "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies 
  \<Longrightarrow> application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the (inverse_application (the (weight p p')) (the (application (the (weight p p')) e))) e\<le> e"
  proof-
    fix p p' e 
    assume "weight p p' \<noteq> None" 
    define u where "u= the (weight p p')"
    show "e\<in>energies \<Longrightarrow> application (the (weight p p')) e \<noteq> None \<Longrightarrow> the (inverse_application (the (weight p p')) (the (application (the (weight p p')) e))) e\<le> e"
    proof-
      assume "e\<in>energies" and "application (the (weight p p')) e \<noteq> None"
      define e' where "e'= upd u e"
      have "(inv_upd u e' e\<le> e) = e' e\<le> upd u e"
        unfolding u_def using \<open>weight p p' \<noteq> None\<close> \<open>application (the (weight p p')) e \<noteq> None\<close> proof(rule galois)
        show \<open>e\<in>energies\<close>  using \<open>e\<in>energies\<close> .
        show \<open>e'\<in>energies\<close> unfolding e'_def using \<open>e\<in>energies\<close>
          using \<open>apply_w p p' e \<noteq> None\<close> \<open>weight p p' \<noteq> None\<close> u_def upd_well_defined by auto 
      qed
      hence "inv_upd u (upd u e) e\<le> e" using e'_def
        by (meson energy_order ordering.eq_iff) 
      thus "the (inverse_application (the (weight p p')) (the (application (the (weight p p')) e))) e\<le> e"
        using u_def by simp
    qed
  qed

  show updates_monotonic:"\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow>e\<in>energies \<Longrightarrow> e e\<le> e' 
  \<Longrightarrow> application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the( application (the (weight p p')) e) e\<le> the (application (the (weight p p')) e')"
  proof-
    fix p p' e e' 
    assume "weight p p' \<noteq> None" and "e\<in>energies" and "e e\<le> e'" and "application (the (weight p p')) e \<noteq> None"
    define u where "u= the (weight p p')"
    define e'' where "e'' = upd u e"
    have "inv_upd u (upd u e) e\<le> e' = (upd u e) e\<le> upd u e'" 
      unfolding u_def using \<open>weight p p' \<noteq> None\<close> proof(rule galois)
      show "apply_w p p' e' \<noteq> None"
        using \<open>application (the (weight p p')) e \<noteq> None\<close> \<open>e e\<le> e'\<close> domain_upw_closed
        using \<open>weight p p' \<noteq> None\<close> by blast 
      show "(upd (the (weight p p')) e)\<in>energies"
        using \<open>e\<in>energies\<close> \<open>weight p p' \<noteq> None\<close> upd_well_defined
        using \<open>apply_w p p' e \<noteq> None\<close> by blast
      show "e'\<in>energies"
        using \<open>e\<in>energies\<close> \<open>e e\<le> e'\<close> upward_closed_energies by auto
    qed

    have "inv_upd u (upd u e) e\<le> e" 
      unfolding u_def using \<open>weight p p' \<noteq> None\<close> \<open>e\<in>energies\<close> \<open>application (the (weight p p')) e \<noteq> None\<close> 
    proof(rule inv_upd_decreasing)
    qed

    hence "inv_upd u (upd u e) e\<le> e'" using \<open>e e\<le> e'\<close> energy_order ordering_def
      by (metis (mono_tags, lifting) partial_preordering.trans) 
    hence "upd u e e\<le> upd u e'" 
      using \<open>inv_upd u (upd u e) e\<le> e' = (upd u e) e\<le> upd u e'\<close> by auto
    thus "the( application (the (weight p p')) e) e\<le> the (application (the (weight p p')) e')"
      using u_def by auto
  qed

  show inverse_monotonic: "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> e\<in>energies \<Longrightarrow> e e\<le> e' 
  \<Longrightarrow> inverse_application (the (weight p p')) e \<noteq> None 
  \<Longrightarrow> the( inverse_application (the (weight p p')) e) e\<le> the (inverse_application (the (weight p p')) e')"
  proof-
    fix p p' e e'
    assume "weight p p' \<noteq> None"
    define u where "u= the (weight p p')"
    show "e\<in>energies \<Longrightarrow> e e\<le> e' \<Longrightarrow> inverse_application (the (weight p p')) e \<noteq> None \<Longrightarrow> the( inverse_application (the (weight p p')) e) e\<le> the (inverse_application (the (weight p p')) e')"
    proof-
      assume "e\<in>energies" and " e e\<le> e'" and " inverse_application (the (weight p p')) e \<noteq> None"

      define e'' where "e'' = inv_upd u e'"
      have "inv_upd u e e\<le> e'' = e e\<le> upd u e''"
        unfolding u_def using \<open>weight p p' \<noteq> None\<close> proof(rule galois)
        show "apply_w p p' e'' \<noteq> None"
          unfolding e''_def using \<open>inverse_application (the (weight p p')) e \<noteq> None\<close>
          using \<open>e \<in> energies\<close> \<open>e e\<le> e'\<close> \<open>weight p p' \<noteq> None\<close> inv_well_defined u_def upward_closed_energies by blast
        show "e\<in>energies" using \<open>e\<in>energies\<close>.
        hence "e'\<in>energies"
          using \<open>e e\<le> e'\<close> energy_order ordering_def
          using upward_closed_energies by blast
        thus "e''\<in>energies"
          unfolding e''_def
          using \<open>weight p p' \<noteq> None\<close> inv_well_defined u_def by blast 
      qed

      have "e' e\<le> upd u e''"
        unfolding e''_def u_def using \<open>weight p p' \<noteq> None\<close> 
      proof(rule upd_inv_increasing)
        from \<open>e\<in>energies\<close> show "e'\<in>energies"
          using \<open>e e\<le> e'\<close> energy_order ordering_def
          using upward_closed_energies by blast
      qed
    
      hence "inv_upd u e e\<le> inv_upd u e'"
        using \<open>inv_upd u e e\<le> e'' = e e\<le> upd u e''\<close> e''_def
        using \<open>e e\<le> e'\<close> energy_order ordering_def
        using upward_closed_energies
        by (metis (no_types, lifting) partial_preordering.trans) 
      thus "the( inverse_application (the (weight p p')) e) e\<le> the (inverse_application (the (weight p p')) e')"
        using u_def by auto
    qed
  qed
qed

text\<open>Galois connections compose. In particular, the ``inverse'' of $u_g$ composed with that of $u_p$ is the ``inverse'' of $u_p \circ u_g$. 
This forms a Galois connection between the set of energies and the reverse image under $u_g$ of the domain of $u_p$, i.e.\ $u_g^{-1} (\text{dom}(u_p))$\<close>

lemma galois_composition:
  assumes "weight g g' \<noteq> None" and "weight p p' \<noteq> None"
  shows  "\<exists>inv. \<forall>e \<in> energies. \<forall>e'\<in> energies. (application (the (weight g g')) e' \<noteq> None 
          \<and> application (the (weight p p')) ((upd (the (weight g g')) e')) \<noteq> None) 
          \<longrightarrow> (order (inv e) e') = (order e (upd (the (weight p p')) ((upd (the (weight g g')) e'))))"
proof
  define inv where "inv \<equiv> \<lambda>x. inv_upd (the (weight g g')) (inv_upd (the (weight p p')) x)"
  show "\<forall>e\<in>energies. \<forall>e'\<in>energies. apply_w g g' e' \<noteq> None \<and> apply_w p p' (upd (the (weight g g')) e') \<noteq> None \<longrightarrow> inv e e\<le> e' = e e\<le> upd (the (weight p p')) (upd (the (weight g g')) e')"
  proof
    fix e 
    assume E: "e\<in>energies"
    show "\<forall>e'\<in>energies. apply_w g g' e' \<noteq> None \<and> apply_w p p' (upd (the (weight g g')) e') \<noteq> None \<longrightarrow> inv e e\<le> e' = e e\<le> upd (the (weight p p')) (upd (the (weight g g')) e')"
    proof
      fix e'
      assume E': "e'\<in>energies"
      show "apply_w g g' e' \<noteq> None \<and> apply_w p p' (upd (the (weight g g')) e') \<noteq> None \<longrightarrow> inv e e\<le> e' = e e\<le> upd (the (weight p p')) (upd (the (weight g g')) e')"
      proof
        assume dom: "apply_w g g' e' \<noteq> None \<and> apply_w p p' (upd (the (weight g g')) e') \<noteq> None"

        define x where "x=inv_upd (the (weight p p')) e "
        have "inv_upd (the (weight g g')) x e\<le> e' = x e\<le> upd (the (weight g g')) e'"
        proof(rule galois)
          show "weight g g' \<noteq> None" using assms by simp
          show "apply_w g g' e' \<noteq> None" using dom by simp
          show "x \<in> energies"
            unfolding x_def using dom
            using E assms(2) inv_well_defined by blast 
          show "e' \<in> energies" using E' .
        qed
        hence A1: "inv e e\<le> e' = inv_upd (the (weight p p')) e e\<le> upd (the (weight g g')) e'"
          unfolding inv_def x_def .

        define y where "y = (upd (the (weight g g')) e')"
        have "inv_upd (the (weight p p')) e e\<le> y = e e\<le> upd (the (weight p p')) y"
        proof(rule galois)
          show "weight p p' \<noteq> None" using assms by simp
          show "apply_w p p' y \<noteq> None" unfolding y_def using dom by simp
          show "e \<in> energies" using E .
          show "y \<in> energies" unfolding y_def
            using E' assms(1) dom upd_well_defined by auto 
        qed
        hence A2: "inv_upd (the (weight p p')) e e\<le> upd (the (weight g g')) e' = e e\<le> upd (the (weight p p')) (upd (the (weight g g')) e')"
          unfolding inv_def y_def .
        show "inv e e\<le> e' = e e\<le> upd (the (weight p p')) (upd (the (weight g g')) e')"
          using A1 A2 by simp
      qed
    qed
  qed
qed

subsection\<open>Properties of the Partial Order\<close>
text\<open>We now establish some properties of the partial order focusing on the set of minimal elements.\<close>

definition energy_Min:: "'energy set \<Rightarrow> 'energy set" where
  "energy_Min A = {e\<in>A . \<forall>e'\<in>A. e\<noteq>e' \<longrightarrow> \<not> (e' e\<le> e)}"

fun enumerate_arbitrary :: "'a set \<Rightarrow> nat \<Rightarrow> 'a"  where
  "enumerate_arbitrary A 0 = (SOME a. a \<in> A)" |
  "enumerate_arbitrary A (Suc n) 
    = enumerate_arbitrary (A - {enumerate_arbitrary A 0}) n"

lemma enumerate_arbitrary_in: 
  shows "infinite A \<Longrightarrow> enumerate_arbitrary A i \<in> A"
proof(induct i arbitrary: A)
  case 0
  then show ?case using enumerate_arbitrary.simps finite.simps some_in_eq by auto 
next
  case (Suc i)
  hence "infinite (A - {enumerate_arbitrary A 0})" using infinite_remove by simp
  hence "enumerate_arbitrary (A - {enumerate_arbitrary A 0}) i \<in> (A - {enumerate_arbitrary A 0})" using Suc.hyps by blast
  hence "enumerate_arbitrary A (Suc i) \<in> (A - {enumerate_arbitrary A 0})" using enumerate_arbitrary.simps by simp
  then show ?case by auto
qed

lemma enumerate_arbitrary_neq:
  shows "infinite A \<Longrightarrow> i < j 
        \<Longrightarrow> enumerate_arbitrary A i \<noteq> enumerate_arbitrary A j"
proof(induct i arbitrary: j A)
  case 0
  then show ?case using enumerate_arbitrary.simps
    by (metis Diff_empty Diff_iff enumerate_arbitrary_in finite_Diff_insert gr0_implies_Suc insert_iff)
next
  case (Suc i)
  hence "\<exists>j'. j = Suc j'"
    by (simp add: not0_implies_Suc) 
  from this obtain j' where "j = Suc j'" by auto
  hence "i < j'" using Suc by simp
  from Suc have "infinite (A - {enumerate_arbitrary A 0})" using infinite_remove by simp
  hence "enumerate_arbitrary (A - {enumerate_arbitrary A 0}) i \<noteq> enumerate_arbitrary (A - {enumerate_arbitrary A 0}) j'" using Suc \<open>i < j'\<close>
    by force
  then show ?case using enumerate_arbitrary.simps
    by (simp add: \<open>j = Suc j'\<close>) 
qed

lemma energy_Min_finite:
  assumes "A \<subseteq> energies"
  shows "finite (energy_Min A)"
proof-
  have "wqo_on order (energy_Min A)" using energy_wqo assms energy_Min_def wqo_on_subset
    by (metis (no_types, lifting) mem_Collect_eq subsetI) 
  hence wqoMin: "(\<forall>f \<in> SEQ (energy_Min A). (\<exists>i j. i < j \<and> order (f i) (f j)))" unfolding wqo_on_def almost_full_on_def good_def by simp
  have "\<not> finite (energy_Min A) \<Longrightarrow> False" 
  proof-
    assume "\<not> finite (energy_Min A)"
    hence "infinite (energy_Min A)"
      by simp

    define f where "f \<equiv> enumerate_arbitrary (energy_Min A)"
    have fneq: "\<And>i j. f i \<in> energy_Min A \<and> (j \<noteq> i \<longrightarrow> f j \<noteq> f i)"
    proof
      fix i j 
      show "f i \<in> energy_Min A" unfolding f_def using enumerate_arbitrary_in \<open>infinite (energy_Min A)\<close> by auto 
      show "j \<noteq> i \<longrightarrow> f j \<noteq> f i" proof
        assume "j \<noteq> i"
        show "f j \<noteq> f i" proof(cases "j < i")
          case True
          then show ?thesis unfolding f_def using enumerate_arbitrary_neq \<open>infinite (energy_Min A)\<close> by auto 
        next
          case False
          hence "i < j" using \<open>j \<noteq> i\<close> by auto
          then show ?thesis unfolding f_def using enumerate_arbitrary_neq \<open>infinite (energy_Min A)\<close>
            by metis 
        qed
      qed
    qed
    hence "\<exists>i j. i < j \<and> order (f i) (f j)" using wqoMin SEQ_def by simp
    thus "False" using energy_Min_def fneq by force
  qed
  thus ?thesis by auto
qed

fun enumerate_decreasing :: "'energy set \<Rightarrow> nat \<Rightarrow> 'energy"  where
  "enumerate_decreasing A 0 = (SOME a. a \<in> A)" |
  "enumerate_decreasing A (Suc n) 
    = (SOME x. (x \<in> A \<and> x e< enumerate_decreasing A n))"

lemma energy_Min_not_empty:
  assumes "A \<noteq> {}" and "A \<subseteq> energies" 
  shows "energy_Min A \<noteq> {}"
proof
  have "wqo_on order A" using energy_wqo assms wqo_on_subset
    by (metis (no_types, lifting)) 
  hence wqoA: "(\<forall>f \<in> SEQ A. (\<exists>i j. i < j \<and> (f i) e\<le> (f j)))" unfolding wqo_on_def almost_full_on_def good_def by simp
  assume "energy_Min A = {}"
  have seq: "enumerate_decreasing A \<in> SEQ A"
    unfolding SEQ_def proof
    show "\<forall>i. enumerate_decreasing A i \<in> A"
    proof
      fix i 
      show "enumerate_decreasing A i \<in> A"
      proof(induct i)
        case 0
        then show ?case using assms
          by (simp add: some_in_eq) 
      next
        case (Suc i)
        show ?case 
        proof(rule ccontr)
          assume "enumerate_decreasing A (Suc i) \<notin> A"
          hence "{x. (x \<in> A \<and> x e< enumerate_decreasing A i)}={}" unfolding enumerate_decreasing.simps
            by (metis (no_types, lifting) empty_Collect_eq someI_ex)
          thus "False"
            using Suc \<open>energy_Min A = {}\<close> energy_Min_def by auto 
        qed
      qed
    qed
  qed

  have "\<not>(\<exists>i j. i < j \<and> (enumerate_decreasing A i) e\<le> (enumerate_decreasing A j))"
  proof-
    have "\<forall>i j. \<not>(i < j \<and> (enumerate_decreasing A i) e\<le> (enumerate_decreasing A j))"
    proof
      fix i
      show "\<forall>j. \<not>(i < j \<and> (enumerate_decreasing A i) e\<le> (enumerate_decreasing A j))"
      proof
        fix j
        have leq: "i < j \<Longrightarrow> (enumerate_decreasing A j) e< (enumerate_decreasing A i)"
        proof(induct "j-i" arbitrary: j i)
          case 0
          then show ?case
            using \<open>i < j\<close> by linarith
        next
          case (Suc x)

          have suc_i: "enumerate_decreasing A (Suc i) e< enumerate_decreasing A i"
          proof-
            have "{x. (x \<in> A \<and> x e< enumerate_decreasing A i)}\<noteq>{} "
            proof
              assume "{x \<in> A. x e< enumerate_decreasing A i} = {}"
              hence "enumerate_decreasing A i \<in> energy_Min A" unfolding energy_Min_def
                using seq by auto 
              thus "False" using \<open>energy_Min A = {}\<close> by auto
            qed
            thus ?thesis unfolding enumerate_decreasing.simps
              by (metis (mono_tags, lifting) empty_Collect_eq verit_sko_ex')
          qed

          have "j - (Suc i) = x" using Suc
            by (metis Suc_diff_Suc nat.inject) 
          then show ?case proof(cases "j = Suc i")
            case True
            then show ?thesis using suc_i
              by simp 
          next
            case False
            hence "enumerate_decreasing A j e< enumerate_decreasing A (Suc i)"
              using Suc \<open>j - (Suc i) = x\<close>
              using Suc_lessI by blast
            then show ?thesis using suc_i energy_order ordering_def
              by (metis (no_types, lifting) ordering_axioms_def partial_preordering.trans) 
          qed
        qed
        
        hence "i <j \<Longrightarrow> \<not>(enumerate_decreasing A i) e\<le> (enumerate_decreasing A j)"
        proof-
          assume "i <j"
          hence "(enumerate_decreasing A j) e< (enumerate_decreasing A i)" using leq by auto
          hence leq: "(enumerate_decreasing A j) e\<le> (enumerate_decreasing A i)" by simp
          have neq: "(enumerate_decreasing A j) \<noteq> (enumerate_decreasing A i)"
            using \<open>(enumerate_decreasing A j) e< (enumerate_decreasing A i)\<close>
            by simp
          show "\<not>(enumerate_decreasing A i) e\<le> (enumerate_decreasing A j)"
          proof
            assume "(enumerate_decreasing A i) e\<le> (enumerate_decreasing A j)"
            hence "(enumerate_decreasing A i) = (enumerate_decreasing A j)" using leq leq energy_order ordering_def
              by (simp add: ordering.antisym) 
            thus "False" using neq by simp
          qed
        qed
        thus "\<not>(i < j \<and> (enumerate_decreasing A i) e\<le> (enumerate_decreasing A j))" by auto
      qed
    qed
    thus ?thesis
      by simp
    qed
  thus "False" using seq wqoA
    by blast 
qed

lemma energy_Min_contains_smaller:
  assumes "a \<in> A" and "A \<subseteq> energies" 
  shows "\<exists>b \<in> energy_Min A. b e\<le> a"
proof-
  define set where "set \<equiv> {e. e \<in> A \<and> e e\<le> a}"
  hence "a \<in> set" using energy_order ordering_def
    using assms ordering.eq_iff by fastforce  
  hence "set \<noteq> {}" by auto
  have "\<And>s. s\<in> set \<Longrightarrow> s\<in> energies" using energy_order set_def assms
    by auto
  hence "energy_Min set \<noteq> {}" using \<open>set \<noteq> {}\<close> energy_Min_not_empty
    by (simp add: subsetI) 
  hence "\<exists>b. b \<in> energy_Min set" by auto
  from this obtain b where "b \<in> energy_Min set" by auto
  hence "\<And>b'. b'\<in> A \<Longrightarrow> b' \<noteq> b \<Longrightarrow> \<not> (b' e\<le> b)"
  proof-
    fix b'
    assume "b' \<in> A"
    assume "b' \<noteq> b"
    show "\<not> (b' e\<le> b)"
    proof
      assume "(b' e\<le> b)"
      hence "b' e\<le> a" using \<open>b \<in> energy_Min set\<close> energy_Min_def energy_order ordering_def
        by (metis (no_types, lifting) local.set_def mem_Collect_eq partial_preordering.trans) 
      hence "b' \<in> set" using \<open>b' \<in> A\<close> set_def by simp
      thus "False" using \<open>b \<in> energy_Min set\<close> energy_Min_def \<open>b' e\<le> b\<close> \<open>b' \<noteq> b\<close> by auto 
    qed
  qed
  hence "b\<in> energy_Min A" using energy_Min_def
    using \<open>b \<in> energy_Min set\<close> local.set_def by auto 
  thus ?thesis using \<open>b \<in> energy_Min set\<close> energy_Min_def set_def by auto
qed

lemma energy_sup_leq_energy_sup:
  assumes "A \<noteq> {}" and "\<And>a. a\<in> A \<Longrightarrow> \<exists>b\<in> B. order a b" and 
          "\<And>a. a\<in> A \<Longrightarrow> a\<in> energies" and "finite A" and "finite B" and "B \<subseteq> energies"
        shows "order (energy_sup A) (energy_sup B)"
proof-
  have A: "\<And>s'. energy_sup A \<in> energies \<and> (\<forall>s. s \<in> A \<longrightarrow> s e\<le> energy_sup A) \<and> (s' \<in> energies \<and>(\<forall>s. s \<in> A \<longrightarrow> s e\<le> s') \<longrightarrow> energy_sup A e\<le> s')" 
  proof(rule bounded_join_semilattice)
    fix s'
    show "finite A" using assms by simp
    show "A \<subseteq> energies" using assms
      by (simp add: subsetI) 
  qed

  have B: "\<And>s'. energy_sup B \<in> energies \<and> (\<forall>s. s \<in> B \<longrightarrow> s e\<le> energy_sup B) \<and> (s' \<in> energies \<and>(\<forall>s. s \<in> B \<longrightarrow> s e\<le> s') \<longrightarrow> energy_sup B e\<le> s')" 
  proof(rule bounded_join_semilattice)
    fix s'
    show " finite B" using assms by simp
    show "B \<subseteq> energies"
      using assms by simp
  qed

  have "energy_sup B \<in> energies \<and> (\<forall>s. s \<in> A \<longrightarrow> s e\<le> energy_sup B)"
  proof
    show "energy_sup B \<in> energies"
      using B by simp
    show " \<forall>s. s \<in> A \<longrightarrow> s e\<le> energy_sup B "
    proof
      fix s
      show "s \<in> A \<longrightarrow> s e\<le> energy_sup B"
      proof
        assume "s \<in> A"
        from this obtain b where "s e\<le> b" and "b \<in> B" using assms
          by blast
        hence "b e\<le> energy_sup B" using B by auto
        thus "s e\<le> energy_sup B" using \<open>s e\<le> b\<close> energy_order ordering_def
          by (metis (mono_tags, lifting) partial_preordering.trans) 
      qed
    qed
  qed
  thus ?thesis using A by auto
qed


subsection\<open>Winning Budgets Revisited\<close>
text\<open>We now redefine attacker winning budgets to only include energies in the set \<open>energies\<close>.\<close>

inductive winning_budget_len::"'energy \<Rightarrow> 'position \<Rightarrow> bool" where
 defender: "winning_budget_len e g" if "e\<in>energies \<and> g \<notin> attacker 
            \<and> (\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> 
                    ((application (the (weight g g')) e)\<noteq> None 
                     \<and> (winning_budget_len (the (application (the (weight g g')) e))) g'))" |
 attacker: "winning_budget_len e g" if "e\<in>energies \<and> g \<in> attacker 
            \<and> (\<exists>g'. (weight g g' \<noteq> None) 
                    \<and> (application (the (weight g g')) e)\<noteq> None 
                    \<and> (winning_budget_len (the (application (the (weight g g')) e)) g'))"

text\<open>We first restate the upward-closure of winning budgets.\<close>

lemma upwards_closure_wb_len:
  assumes "winning_budget_len e g" and "e e\<le> e'"
  shows "winning_budget_len e' g"
using assms proof (induct arbitrary: e' rule: winning_budget_len.induct)
  case (defender e g)
  have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          application (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e')) g')" 
  proof
    fix g'
    show " weight g g' \<noteq> None \<longrightarrow>
          application (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e')) g'" 
    proof
      assume "weight g g' \<noteq> None"
      hence A: "application (the (weight g g')) e \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e)) g'" using assms(1) winning_budget_len.simps defender by blast
      show "application (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e')) g'" 
      proof
        show "application (the (weight g g')) e' \<noteq> None" using domain_upw_closed assms(2) A defender \<open>weight g g' \<noteq> None\<close> by blast
        have "order (the (application (the (weight g g')) e)) (the (application (the (weight g g')) e'))" using assms A updates_monotonic
          using \<open>weight g g' \<noteq> None\<close> defender.hyps defender.prems by presburger  
        thus "winning_budget_len (the (application (the (weight g g')) e')) g'" using defender \<open>weight g g' \<noteq> None\<close> by blast
      qed
    qed
  qed
thus ?case using winning_budget_len.intros(1) defender
  by (meson upward_closed_energies)
next
  case (attacker e g)
  from this obtain g' where G: "weight g g' \<noteq> None \<and>
          application (the (weight g g')) e \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e)) g' \<and>
          (\<forall>x. order (the (application (the (weight g g')) e)) x \<longrightarrow> winning_budget_len x g')" by blast
  have "weight g g' \<noteq> None \<and>
          application (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) e')) g'" 
  proof
    show "weight g g' \<noteq> None" using G by auto
    show "application (the (weight g g')) e' \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) e')) g' " 
    proof
      show "application (the (weight g g')) e' \<noteq> None" using G  domain_upw_closed assms attacker by blast
      have "order (the (application (the (weight g g')) e)) (the (application (the (weight g g')) e'))" using assms G updates_monotonic
        using attacker.hyps attacker.prems by blast
      thus "winning_budget_len (the (application (the (weight g g')) e')) g' " using G by blast
    qed
  qed
  thus ?case using winning_budget_len.intros(2) attacker
    using upward_closed_energies by blast
qed

text\<open>We now show that this definition is consistent with our previous definition of winning budgets.
We show this by well-founded induction.\<close>

abbreviation "reachable_positions_len s g e \<equiv> {(g',e') \<in> reachable_positions s g e . e'\<in>energies}"

lemma winning_bugget_len_is_wb:
  assumes "nonpos_winning_budget = winning_budget"
  shows "winning_budget_len e g = (winning_budget e g \<and>  e \<in>energies)"
proof
  assume "winning_budget_len e g"
  show "winning_budget e g \<and> e \<in>energies"
  proof
    have "winning_budget_ind e g" 
      using \<open>winning_budget_len e g\<close> proof(rule winning_budget_len.induct)
      show "\<And>e g. e \<in>energies \<and>
           g \<notin> attacker \<and>
           (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                 apply_w g g' e \<noteq> None \<and>
                 winning_budget_len (upd (the (weight g g')) e) g' \<and>
                 winning_budget_ind (upd (the (weight g g')) e) g') \<Longrightarrow>
           winning_budget_ind e g"
        using winning_budget_ind.simps
        by meson 
      show "\<And>e g. e \<in>energies \<and>
           g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 apply_w g g' e \<noteq> None \<and>
                 winning_budget_len (upd (the (weight g g')) e) g' \<and>
                 winning_budget_ind (upd (the (weight g g')) e) g') \<Longrightarrow>
           winning_budget_ind e g "
        using winning_budget_ind.simps
        by meson 
    qed
    thus "winning_budget e g" using assms inductive_winning_budget
      by fastforce 
    show "e \<in>energies" using \<open>winning_budget_len e g\<close> winning_budget_len.simps by blast 
  qed
next
  show "winning_budget e g \<and> e \<in>energies \<Longrightarrow> winning_budget_len e g" 
  proof-
    assume A: "winning_budget e g \<and> e \<in>energies"
    hence "winning_budget_ind e g" using assms inductive_winning_budget by fastforce
    show "winning_budget_len e g" 
    proof-

      define wb where "wb \<equiv> \<lambda>(g,e). winning_budget_len e g"

      from A have "\<exists>s. attacker_winning_strategy s e g" using winning_budget.simps by blast
      from this obtain s where S: "attacker_winning_strategy s e g" by auto

      have "reachable_positions_len s g e \<subseteq> reachable_positions s g e" by auto
      hence "wfp_on (strategy_order s) (reachable_positions_len s g e)" 
        using strategy_order_well_founded S
        using Restricted_Predicates.wfp_on_subset by blast
      hence "inductive_on (strategy_order s) (reachable_positions_len s g e)"
        by (simp add: wfp_on_iff_inductive_on)

      hence "wb (g,e)" 
      proof(rule inductive_on_induct)
        show "(g,e) \<in> reachable_positions_len s g e"
          unfolding reachable_positions_def proof-
          have "lfinite LNil \<and>
             llast (LCons g LNil) = g \<and>
             valid_play (LCons g LNil) \<and> play_consistent_attacker s (LCons g LNil) e \<and>
            Some e = energy_level e (LCons g LNil) (the_enat (llength LNil))"
            using valid_play.simps play_consistent_attacker.simps energy_level.simps
            by (metis lfinite_code(1) llast_singleton llength_LNil neq_LNil_conv the_enat_0) 
          thus "(g, e) \<in> {(g', e').
        (g', e')
        \<in> {(g', e') |g' e'.
            \<exists>p. lfinite p \<and>
                llast (LCons g p) = g' \<and>
                valid_play (LCons g p) \<and>
                play_consistent_attacker s (LCons g p) e \<and>
                Some e' = energy_level e (LCons g p) (the_enat (llength p))} \<and>
         e'\<in>energies}" using A

            by blast 
        qed

        show "\<And>y. y \<in> reachable_positions_len s g e \<Longrightarrow>
              (\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
        proof-
          fix y 
          assume "y \<in> reachable_positions_len s g e"
          hence "\<exists>e' g'. y = (g', e')" using reachable_positions_def by auto
          from this obtain e' g' where "y = (g', e')" by auto

          hence y_len: "(\<exists>p. lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p))))
                \<and> e'\<in>energies"
            using \<open>y \<in> reachable_positions_len s g e\<close> unfolding reachable_positions_def
            by auto 
          from this obtain p where P: "(lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e) 
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p)))" by auto
       
          show "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
          proof-
            assume ind: "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x)"
            have "winning_budget_len e' g'" 
            proof(cases "g' \<in> attacker")
              case True 
              then show ?thesis 
              proof(cases "deadend g'")
                case True (* wiederspruchsbeweis *)
                hence "attacker_stuck (LCons g p)" using \<open>g' \<in> attacker\<close> P
                  by (meson A defender_wins_play_def attacker_winning_strategy.elims(2)) 
                hence "defender_wins_play e (LCons g p)" using defender_wins_play_def by simp
                have "\<not>defender_wins_play e (LCons g p)" using P A S by simp
                then show ?thesis using \<open>defender_wins_play e (LCons g p)\<close> by simp
              next
                case False (* nehme s e' g' und wende ind.hyps. darauf an *)
                hence "(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None" using S attacker_winning_strategy.simps
                  by (simp add: True attacker_strategy_def)

                define x where "x = (the (s e' g'), the (apply_w g' (the (s e' g')) e'))"
                define p' where "p' =  (lappend p (LCons (the (s e' g')) LNil))"
                hence "lfinite p'" using P by simp
                have "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
                  by (simp add: llast_LCons)

                have "the_enat (llength p') > 0" using P
                  by (metis LNil_eq_lappend_iff \<open>lfinite p'\<close> bot_nat_0.not_eq_extremum enat_0_iff(2) lfinite_conv_llength_enat llength_eq_0 llist.collapse(1) llist.distinct(1) p'_def the_enat.simps) 
                hence "\<exists>i. Suc i = the_enat (llength p')"
                  using less_iff_Suc_add by auto 
                from this obtain i where "Suc i = the_enat (llength p')" by auto
                hence "i = the_enat (llength p)" using p'_def P                     
                  by (metis Suc_leI \<open>lfinite p'\<close> length_append_singleton length_list_of_conv_the_enat less_Suc_eq_le less_irrefl_nat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend not_less_less_Suc_eq)
                hence "Some e' = (energy_level e (LCons g p) i)" using P by simp

                have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                proof
                  show "lfinite (LCons g p)" using P by simp
                  show "i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                  proof
                    show "i < the_enat (llength (LCons g p))" using \<open>i = the_enat (llength p)\<close> P
                      by (metis \<open>lfinite (LCons g p)\<close> length_Cons length_list_of_conv_the_enat lessI list_of_LCons) 
                    show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P \<open>i = the_enat (llength p)\<close>
                      using S defender_wins_play_def by auto
                  qed
                qed

                hence "Some e' = (energy_level e (LCons g p') i)" using p'_def energy_level_append P \<open>Some e' = (energy_level e (LCons g p) i)\<close>
                  by (metis lappend_code(2))
                hence "energy_level e (LCons g p') i \<noteq> None"
                  by (metis option.distinct(1))

                have "enat (Suc i) = llength p'" using \<open>Suc i = the_enat (llength p')\<close>
                  by (metis \<open>lfinite p'\<close> lfinite_conv_llength_enat the_enat.simps)
                also have "... < eSuc (llength p')"
                  by (metis calculation iless_Suc_eq order_refl) 
                also have "... = llength (LCons g p')" using \<open>lfinite p'\<close> by simp
                finally have "enat (Suc i) < llength (LCons g p')".

                have "(lnth (LCons g p) i) = g'" using \<open>i = the_enat (llength p)\<close> P
                  by (metis lfinite_conv_llength_enat llast_conv_lnth llength_LCons the_enat.simps) 
                hence "(lnth (LCons g p') i) = g'" using p'_def
                  by (metis P \<open>i = the_enat (llength p)\<close> enat_ord_simps(2) energy_level.elims lessI lfinite_llength_enat lnth_0 lnth_Suc_LCons lnth_lappend1 the_enat.simps) 

                have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" 
                  using \<open>Suc i = the_enat (llength p')\<close> by simp
                also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
                  using energy_level.simps \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>energy_level e (LCons g p') i \<noteq> None\<close>
                  by (meson leD)
                also have "... =  apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) e'" using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
                  by (metis option.sel) 
                also have "... =  apply_w (lnth (LCons g p') i) (the (s e' g')) e'" using p'_def \<open>enat (Suc i) = llength p'\<close>
                  by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>llast (LCons g p') = the (s e' g')\<close> llast_conv_lnth) 
                also have  "... =  apply_w g' (the (s e' g')) e'" using \<open>(lnth (LCons g p') i) = g'\<close> by simp
                finally have "energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'" .
            
                have P': "lfinite p'\<and>
             llast (LCons g p') = (the (s e' g')) \<and>
             valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
            Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                proof
                  show "lfinite p'" using p'_def P by simp
                  show "llast (LCons g p') = the (s e' g') \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                  proof
                    show "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
                      by (simp add: llast_LCons) 
                    show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                    proof
                      show "valid_play (LCons g p')" using p'_def P
                        using \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> valid_play.intros(2) valid_play_append by auto
                      show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                      proof
                        have "(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)" using p'_def
                          by simp
                        have "play_consistent_attacker s (lappend (LCons g p) (LCons (the (s e' g')) LNil)) e"
                        proof (rule play_consistent_attacker_append_one)
                          show "play_consistent_attacker s (LCons g p) e"
                            using P by auto
                          show "lfinite (LCons g p)" using P by auto
                          show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                            using A by auto 
                          show "valid_play (lappend (LCons g p) (LCons (the (s e' g')) LNil))" 
                            using \<open>valid_play (LCons g p')\<close> \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                          show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                          proof
                            assume "llast (LCons g p) \<in> attacker"
                            show "Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                              using \<open>llast (LCons g p) \<in> attacker\<close> P
                              by (metis One_nat_def \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> diff_Suc_1' eSuc_enat lfinite_llength_enat llength_LCons option.collapse option.sel the_enat.simps) 
                          qed
                        qed
                        thus "play_consistent_attacker s (LCons g p') e" using \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                    
                        show "Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                          by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>enat (Suc i) = llength p'\<close> \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> \<open>play_consistent_attacker s (LCons g p') e\<close> \<open>valid_play (LCons g p')\<close> S defender_wins_play_def diff_Suc_1 eSuc_enat option.collapse attacker_winning_strategy.elims(2) the_enat.simps)
                      qed
                    qed
                  qed
                qed

                have x_len: "(upd (the (weight g' (the (s e' g')))) e') \<in>energies" using y_len
                  by (metis P' \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> option.distinct(1) upd_well_defined)
                hence "x \<in> reachable_positions_len s g e" using P' reachable_positions_def x_def by auto

                have "(apply_w g' (the (s e' g')) e') \<noteq> None" using P'
                  by (metis \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> option.distinct(1)) 
    
                have "Some (the (apply_w g' (the (s e' g')) e')) = apply_w g' (the (s e' g')) e' \<and> (if g' \<in> attacker then Some (the (s e' g')) = s e' g' else weight g' (the (s e' g')) \<noteq> None)"
                  using \<open>(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None\<close> \<open>(apply_w g' (the (s e' g')) e') \<noteq> None\<close> by simp
                hence "strategy_order s x y" unfolding strategy_order_def using x_def \<open>y = (g', e')\<close>
                  by blast
                hence "wb x" using ind \<open>x \<in> reachable_positions_len s g e\<close> by simp
                hence "winning_budget_len (the (apply_w g' (the (s e' g')) e')) (the (s e' g'))" using wb_def x_def by simp
                then show ?thesis using \<open>g' \<in> attacker\<close> winning_budget_ind.simps
                  by (meson \<open>apply_w g' (the (s e' g')) e' \<noteq> None\<close> \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> winning_budget_len.attacker y_len) 
              qed
            next
              case False
              hence "g' \<notin> attacker \<and>
            (\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g'')"
              proof
                show "\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g''"
                proof
                  fix g''
                  show "weight g' g'' \<noteq> None \<longrightarrow>
           apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g'' "
                  proof
                    assume "weight g' g'' \<noteq> None"
                    show "apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g''"
                    proof
                      show "apply_w g' g'' e' \<noteq> None"
                      proof
                        assume "apply_w g' g'' e' = None"
                        define p' where "p' \<equiv> (LCons g (lappend p (LCons g'' LNil)))"
                        hence "lfinite p'" using P by simp
                        have "\<exists>i. llength p = enat i" using P
                          by (simp add: lfinite_llength_enat) 
                        from this obtain i where "llength p = enat i" by auto
                        hence "llength (lappend p (LCons g'' LNil)) = enat (Suc i)"
                          by (simp add: \<open>llength p = enat i\<close> eSuc_enat iadd_Suc_right)
                        hence "llength p' = eSuc (enat(Suc i))" using p'_def
                          by simp 
                        hence "the_enat (llength p') = Suc (Suc i)"
                          by (simp add: eSuc_enat)
                        hence "the_enat (llength p') - 1 = Suc i"
                          by simp 
                        hence "the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))"
                          using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close>
                          by simp

                        have "(lnth p' i) = g'" using p'_def \<open>llength p = enat i\<close> P
                          by (smt (verit) One_nat_def diff_Suc_1' enat_ord_simps(2) energy_level.elims lessI llast_conv_lnth llength_LCons lnth_0 lnth_LCons' lnth_lappend the_enat.simps)
                        have "(lnth p' (Suc i)) = g''" using p'_def \<open>llength p = enat i\<close>
                          by (metis \<open>llength p' = eSuc (enat (Suc i))\<close> lappend.disc(2) llast_LCons llast_conv_lnth llast_lappend_LCons llength_eq_enat_lfiniteD llist.disc(1) llist.disc(2))
                        have "p' = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                        hence "the (energy_level e p' i) = the (energy_level e (lappend (LCons g p) (LCons g'' LNil)) i)" by simp
                        also have "... = the (energy_level e (LCons g p) i)" using \<open>llength p = enat i\<close> energy_level_append P
                          by (metis diff_Suc_1 eSuc_enat lessI lfinite_LConsI llength_LCons option.distinct(1) the_enat.simps) 
                        also have "... = e'" using P
                          by (metis \<open>llength p = enat i\<close> option.sel the_enat.simps) 
                        finally have "the (energy_level e p' i) = e'" . 
                        hence "apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None" using \<open>apply_w g' g'' e'=None\<close> \<open>(lnth p' i) = g'\<close> \<open>(lnth p' (Suc i)) = g''\<close> by simp

                        have "energy_level e p' (the_enat (llength p') - 1) = 
                          energy_level e p' (the_enat (llength (lappend p (LCons g'' LNil))))" 
                          using \<open>the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))\<close>
                          by simp 
                        also have "... = energy_level e p' (Suc i)" using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close> by simp
                        also have "... = (if energy_level e p' i = None \<or> llength p' \<le> enat (Suc i) then None
                                      else apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)))" using energy_level.simps by simp
                        also have "... = None " using \<open>apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None\<close>
                          by simp
                        finally have "energy_level e p' (the_enat (llength p') - 1) = None" .
                        hence "defender_wins_play e p'" unfolding defender_wins_play_def by simp

                        have "valid_play p'"
                          by (metis P \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> \<open>weight g' g'' \<noteq> None\<close> energy_game.valid_play.intros(2) energy_game.valid_play_append lfinite_LConsI)

                        have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                        proof(rule play_consistent_attacker_append_one)
                          show "play_consistent_attacker s (LCons g p) e" 
                            using P by simp
                          show "lfinite (LCons g p)" using P by simp
                          show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                            using P
                            by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                          show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                            using \<open>valid_play p'\<close> \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                          show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some g'' =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                            using False P by simp
                        qed
                        hence "play_consistent_attacker s p' e"
                          using \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                        hence "\<not>defender_wins_play e p'" using \<open>valid_play p'\<close> p'_def S by simp
                        thus "False" using \<open>defender_wins_play e p'\<close> by simp
                      (* widerspruch weil in reachable und sonst defender_wins_play *)
                      qed

                      define x where "x = (g'', the (apply_w g' g'' e'))"
                      have "wb x" 
                      proof(rule ind)
                        have X: "(\<exists>p. lfinite p \<and>
             llast (LCons g p) = g'' \<and>
             valid_play (LCons g p) \<and> play_consistent_attacker s (LCons g p) e \<and>
            Some (the (apply_w g' g'' e')) = energy_level e (LCons g p) (the_enat (llength p)))"
                        proof
                          define p' where "p' = lappend p (LCons g'' LNil)"
                          show "lfinite p' \<and>
     llast (LCons g p') = g'' \<and>
     valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                          proof
                            show "lfinite p'" using P p'_def by simp
                            show "llast (LCons g p') = g'' \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                            proof
                              show "llast (LCons g p') = g''" using p'_def
                                by (metis \<open>lfinite p'\<close> lappend.disc_iff(2) lfinite_lappend llast_LCons llast_lappend_LCons llast_singleton llist.discI(2))
                              show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                              proof
                                show "valid_play (LCons g p')" using p'_def P
                                  using \<open>weight g' g'' \<noteq> None\<close> lfinite_LCons valid_play.intros(2) valid_play_append by auto
                                show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p')) "
                                proof

                                  have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                                  proof(rule play_consistent_attacker_append_one)
                                    show "play_consistent_attacker s (LCons g p) e" 
                                      using P by simp
                                    show "lfinite (LCons g p)" using P by simp
                                    show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                                      using P
                                      by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                                    show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                                      using \<open>valid_play (LCons g p')\<close> p'_def by simp
                                    show "llast (LCons g p) \<in> attacker \<longrightarrow>
                                        Some g'' =
                                        s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                                      using False P by simp
                                  qed
                                  thus "play_consistent_attacker s (LCons g p') e" using p'_def
                                    by (simp add: lappend_code(2)) 

                                  have "\<exists>i. Suc i = the_enat (llength p')" using p'_def \<open>lfinite p'\<close>
                                    by (metis P length_append_singleton length_list_of_conv_the_enat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend)
                                  from this obtain i where "Suc i = the_enat (llength p')" by auto
                                  hence "i = the_enat (llength p)" using p'_def
                                    by (smt (verit) One_nat_def \<open>lfinite p'\<close> add.commute add_Suc_shift add_right_cancel length_append length_list_of_conv_the_enat lfinite_LNil lfinite_lappend list.size(3) list.size(4) list_of_LCons list_of_LNil list_of_lappend plus_1_eq_Suc)  
                                  hence "Suc i = llength (LCons g p)"
                                    using P eSuc_enat lfinite_llength_enat by fastforce
                                  have "(LCons g p') = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                                  have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and>  energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                                  proof
                                    show "lfinite (LCons g p)" using P by simp
                                    show " i < the_enat (llength (LCons g p)) \<and>
    energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None "
                                    proof
                                      have "(llength p') = llength (LCons g p)" using p'_def
                                        by (metis P \<open>lfinite p'\<close> length_Cons length_append_singleton length_list_of lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend) 
                                      thus "i < the_enat (llength (LCons g p))" using \<open>Suc i = the_enat (llength p')\<close>
                                        using lessI by force 
                                      show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                                        by (meson S energy_game.defender_wins_play_def energy_game.play_consistent_attacker.intros(2) attacker_winning_strategy.simps)
                                    qed
                                  qed
                                  hence "energy_level e (LCons g p') i \<noteq> None"
                                    using energy_level_append
                                    by (smt (verit) Nat.lessE Suc_leI \<open>LCons g p' = lappend (LCons g p) (LCons g'' LNil)\<close> diff_Suc_1 energy_level_nth)  
                                  have "enat (Suc i) < llength (LCons g p')" 
                                    using \<open>Suc i = the_enat (llength p')\<close>
                                    by (metis Suc_ile_eq \<open>lfinite p'\<close> ldropn_Suc_LCons leI lfinite_conv_llength_enat lnull_ldropn nless_le the_enat.simps) 
                                  hence  el_prems: "energy_level e (LCons g p') i \<noteq> None \<and> llength (LCons g p') > enat (Suc i)" using \<open>energy_level e (LCons g p') i \<noteq> None\<close> by simp

                                  have "(lnth (LCons g p') i) = lnth (LCons g p) i" 
                                    unfolding \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close> using \<open>i = the_enat (llength p)\<close> lnth_lappend1
                                    by (metis A enat_ord_simps(2) length_list_of length_list_of_conv_the_enat)
                                  have "lnth (LCons g p) i = llast (LCons g p)" using \<open>Suc i = llength (LCons g p)\<close>
                                    by (metis enat_ord_simps(2) lappend_LNil2 ldropn_LNil ldropn_Suc_conv_ldropn ldropn_lappend lessI less_not_refl llast_ldropn llast_singleton)
                                  hence "(lnth (LCons g p') i) = g'" using P
                                    by (simp add: \<open>lnth (LCons g p') i = lnth (LCons g p) i\<close>) 
                                  have "(lnth (LCons g p') (Suc i)) = g''"
                                    using p'_def \<open>Suc i = the_enat (llength p')\<close>
                                    by (smt (verit) \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>lfinite p'\<close> \<open>llast (LCons g p') = g''\<close> lappend_snocL1_conv_LCons2 ldropn_LNil ldropn_Suc_LCons ldropn_Suc_conv_ldropn ldropn_lappend2 lfinite_llength_enat llast_ldropn llast_singleton the_enat.simps wlog_linorder_le)

                                  have "energy_level e (LCons g p) i = energy_level e (LCons g p') i" 
                                    using energy_level_append A \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close>
                                    by presburger
                                  hence "Some e' = (energy_level e (LCons g p') i)" 
                                    using P \<open>i = the_enat (llength p)\<close>
                                    by argo 

                                  have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" using \<open>Suc i = the_enat (llength p')\<close> by simp
                                  also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
                                    using energy_level.simps el_prems
                                    by (meson leD) 
                                  also have "... = apply_w g' g'' (the (energy_level e (LCons g p') i))" 
                                    using \<open>(lnth (LCons g p') i) = g'\<close> \<open>(lnth (LCons g p') (Suc i)) = g''\<close> by simp
                                  finally have "energy_level e (LCons g p') (the_enat (llength p')) = (apply_w g' g'' e')" 
                                    using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
                                    by (metis option.sel) 
                                  thus "Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                                    using \<open>apply_w g' g'' e' \<noteq> None\<close> by auto
                                qed
                              qed
                            qed
                          qed
                        qed

                        have x_len: "(upd (the (weight g' g'')) e') \<in>energies" using y_len
                          using \<open>apply_w g' g'' e' \<noteq> None\<close> \<open>weight g' g'' \<noteq> None\<close> upd_well_defined by auto 

                        thus "x \<in> reachable_positions_len s g e"
                          using X x_def reachable_positions_def
                          by (simp add: mem_Collect_eq) 

                        have "Some (the (apply_w g' g'' e')) = apply_w g' g'' e' \<and>
         (if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                        proof
                          show "Some (the (apply_w g' g'' e')) = apply_w g' g'' e'"
                            using \<open>apply_w g' g'' e' \<noteq> None\<close> by auto
                          show "(if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                            using False
                            by (simp add: \<open>weight g' g'' \<noteq> None\<close>) 
                        qed
                        thus "strategy_order s x y" using strategy_order_def x_def \<open>y = (g', e')\<close>
                          by simp
                      qed

                      thus "winning_budget_len (the (apply_w g' g'' e')) g'' " using x_def wb_def 
                        by force 
                    qed
                  qed
                qed
              qed
              thus ?thesis using winning_budget_len.intros y_len by blast
            qed
            thus "wb y" using \<open>y = (g', e')\<close> wb_def by simp
          qed
        qed
      qed
      thus ?thesis using wb_def by simp
    qed
  qed
qed

end
end