theory PairToEuclidIntegral
imports "HOL-Analysis.Analysis"
begin

lemma real_pair_basis: "Basis = {(1::real,0::real), (0,1)}"
  by (simp add: Basis_prod_def insert_commute)

lemma not_in_sum_zero:
      fixes s::"('a::euclidean_space) set" and
            x::"'a"
      assumes "i \<in> Basis"
              "i \<notin> s"
              "s \<subseteq> Basis"
      shows "(\<Sum>b\<in>s. (x \<bullet> b) *\<^sub>R b) \<bullet> i = 0"
      proof (simp add: Inner_Product.real_inner_class.inner_sum_left)
        have "\<forall>b\<in>s. ((x \<bullet> b) *\<^sub>R b) \<bullet> i = 0"
          using assms inner_not_same_Basis by auto
        then show "(\<Sum>b\<in>s. x \<bullet> b * (b \<bullet> i)) = 0"
             by (simp add: sum.neutral)
      qed

lemma rest_of_a_k_is_0: "\<And>k. k \<in> Basis \<Longrightarrow>  (\<Sum>b\<in>((Basis - {i}) - {j})- {k}. (a \<bullet> b) *\<^sub>R b) \<bullet> k = 0"
  using not_in_sum_zero[of _ "((Basis - {i}) - {j}) - {k}" for k "a"] 
  by auto

lemma inj_on_inj_on_image:
      assumes "\<forall>s. inj_on f s" (*this is a needed assumption*)
      shows "inj_on (%s. f ` s) S"
      apply (simp add: inj_on_def image_def)
      proof
        {
          fix x y
          assume x_in:"x \<in> S"
          assume y_in: "y \<in> S"
          assume imgs_eq: "{y. \<exists>x\<in>x. y = f x} = {ya. \<exists>x\<in>y. ya = f x}"
          then have imgs_eq_ext: "\<forall>z. (\<exists>x\<in>x. z = f x) = (\<exists>x\<in>y. z = f x)" by auto
          have "x= y"
            proof
              show "x \<subseteq> y"
                   apply (simp add: Set.subset_iff)
                   using x_in and y_in  and imgs_eq_ext and assms and inj_on_def by auto
              show "y \<subseteq> x"
                   apply (simp add: Set.subset_iff)
                   using x_in and y_in  and imgs_eq_ext and assms and inj_on_def by auto
            qed
        }
        then show "\<And>x. x \<in> S \<Longrightarrow> \<forall>y\<in>S. {y. \<exists>x\<in>x. y = f x} = {ya. \<exists>x\<in>y. ya = f x} \<longrightarrow> x = y" by auto
      qed

lemma inj_on_pairs:
  assumes "inj_on f (fst ` S)" "inj_on g (snd ` S)"
  shows "inj_on (%p. (f (fst p), g (snd p))) S"
  unfolding inj_on_def image_def
  by (metis Pair_inject assms image_eqI inj_onD prod_eqI)

lemma bounded_dist_img_bounded:
      assumes "bounded (s::'a::euclidean_space set)"
      shows "bounded (dist 0 ` s)"
      using assms
      apply (auto simp add: bounded_def)
      proof -
        fix x e
        assume "\<forall>y\<in>s. dist x y \<le> e"
        then have " \<forall>y'\<in>s. dist 0 (dist 0 y') \<le> e + dist 0 x"
             apply (auto simp add: Real_Vector_Spaces.dist_norm_class.dist_norm)
             by (smt norm_minus_commute norm_triangle_sub)
        then show "\<And>x e. \<forall>y\<in>s. dist x y \<le> e \<Longrightarrow> \<exists>x e. \<forall>y\<in>s. dist x (norm y) \<le> e" by (metis dist_0_norm)
      qed

locale twoD_Space =
     fixes i j::"'a::{euclidean_space}" and
           F_b'::"'a => real" and
           Dy::"'a set" and
           pair_to_euclid:: "( real*real) \<Rightarrow> 'a" and
           euclid_to_pair:: " 'a \<Rightarrow> ( real*real)"
     assumes twoD_space: "Basis = {i , j}" and
             pair_to_euclid_def: "pair_to_euclid =  (%p.  ((fst p)  *\<^sub>R i) + ((snd p) *\<^sub>R j))" and
             euclid_to_pair_def: "euclid_to_pair =  (%a. (a \<bullet> i,a \<bullet> j))" and
             norm_i_j_sq_ubound: "\<And>x. norm (( x \<bullet> i) *\<^sub>R i + ( x \<bullet> j) *\<^sub>R j) \<le> sqrt ( ( x \<bullet> i)\<^sup>2  +  ( x \<bullet> j)\<^sup>2)" and
             bounded_euclid_set_imp_bounded_pair_set: "\<And>s. bounded s \<Longrightarrow> bounded (euclid_to_pair ` s)"and  (*needed for euclid ball is pair ball ball lemma*)
             Base_vecs: "i \<in> Basis" "j \<in> Basis" "\<not>(i = j)" and

             Dy_is2d: "Dy \<subseteq> {v. \<exists>a b. v = a *\<^sub>R i + b *\<^sub>R j}" (*THis is redundant*)
begin

lemma inj_pair_to_euclid_on_pairs:
      fixes D_pair
      shows "inj_on pair_to_euclid D_pair"
      apply (simp add: inj_on_def pair_to_euclid_def)
   proof-
     {
       fix x y :: "real*real"
       assume "x \<in> D_pair"
       assume "y \<in> D_pair"
       assume ass: "fst x *\<^sub>R i + snd x *\<^sub>R j = fst y *\<^sub>R i + snd y *\<^sub>R j"
       then have i_comp_eq: "(fst x *\<^sub>R i + snd x *\<^sub>R j) \<bullet> i = (fst y *\<^sub>R i + snd y *\<^sub>R j) \<bullet> i" by auto
       have fst_x: "(fst x *\<^sub>R i + snd x *\<^sub>R j) \<bullet> i = fst x"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       have "(fst y *\<^sub>R i + snd y *\<^sub>R j) \<bullet> i = fst y"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       then have fst_x_eq_fst_y: "fst x = fst y" using Base_vecs and fst_x and i_comp_eq by auto
       have j_comp_eq: "(fst x *\<^sub>R i + snd x *\<^sub>R j) \<bullet> j = (fst y *\<^sub>R i + snd y *\<^sub>R j) \<bullet> j" using ass by auto
       have snd_x: "(fst x *\<^sub>R i + snd x *\<^sub>R j) \<bullet> j = snd x"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       have "(fst y *\<^sub>R i + snd y *\<^sub>R j) \<bullet> j = snd y"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       then have snd_x_eq_snd_y: "snd x = snd y" using Base_vecs and snd_x and j_comp_eq by auto
       have  "x = y" using fst_x_eq_fst_y and snd_x_eq_snd_y by (simp add: prod.expand)
     }
     then show "\<forall>x\<in>D_pair. \<forall>y\<in>D_pair. fst x *\<^sub>R i + snd x *\<^sub>R j = fst y *\<^sub>R i + snd y *\<^sub>R j \<longrightarrow> x = y" by auto
   qed

lemma inj_pair_to_euclid:
      shows "inj pair_to_euclid"
      apply (simp add: inj_on_def pair_to_euclid_def)
   proof-
     {
       fix a b a' b' :: "real"
       assume ass: "a *\<^sub>R i + b *\<^sub>R j = a' *\<^sub>R i + b' *\<^sub>R j"
       then have i_comp_eq: "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> i = (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> i" by auto
       have fst_x: "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> i = a"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       have "(a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> i = a'"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       then have fst_x_eq_fst_y: "a = a'" using Base_vecs and fst_x and i_comp_eq by auto
       have j_comp_eq: "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> j = (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> j" using ass by auto
       have snd_x: "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> j = b"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       have "(a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> j = b'"
            using Base_vecs
            by (simp add: real_inner_class.inner_add_left inner_not_same_Basis)
       then have snd_x_eq_snd_y: "b = b'" using Base_vecs and snd_x and j_comp_eq by auto
       have  "a = a' \<and> b = b'" using fst_x_eq_fst_y and snd_x_eq_snd_y by auto
     }
     then show " \<forall>a b a' b'. a *\<^sub>R i + b *\<^sub>R j = a' *\<^sub>R i + b' *\<^sub>R j \<longrightarrow> a = a' \<and> b = b'"
          by auto
   qed

lemma surj_pair_to_euclid_twoD:
      shows "surj pair_to_euclid"
      apply (simp add: pair_to_euclid_def surj_def)
   proof
       fix y::'a
       show "\<exists>a b. y = a *\<^sub>R i + b *\<^sub>R j"
            using euclidean_representation[of"y"] Base_vecs
            apply (simp add: twoD_space sum.insert_remove)
            by metis
   qed

lemma surj_euclid_to_pair:
      shows "surj euclid_to_pair"
      apply (simp add: euclid_to_pair_def surj_def)
   proof -
       {
         fix a b::real
         have "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> i = a \<and>  (a *\<^sub>R i + b *\<^sub>R j) \<bullet> j = b"
              apply (simp add: inner_add_left)
              using Base_vecs by (auto simp add: inner_not_same_Basis)
         then have "\<exists>x. a = x \<bullet> i \<and> b = x \<bullet> j"
              using euclidean_representation[of"y"] Base_vecs
              apply (simp add: twoD_space sum.insert_remove)
              by metis
       }
       then show " \<forall>a b. \<exists>x. a = x \<bullet> i \<and> b = x \<bullet> j" by auto
   qed

lemma pair_to_euclid_inv_euclid_to_pair:
      (*This should be pair_to_euclid = inv_into Dy euclid_to_pair *)
      shows "pair_to_euclid = inv_into {v. \<exists>a b. v = a *\<^sub>R i + b *\<^sub>R j} euclid_to_pair"
      apply (auto simp: euclid_to_pair_def pair_to_euclid_def inv_into_def)
      proof
        fix p
        have 0: "\<exists>!x. (\<exists>a b. x = a *\<^sub>R i + b *\<^sub>R j) \<and> (x \<bullet> i, x \<bullet> j) = p"
             proof
                let ?a = "(fst p *\<^sub>R i + snd p *\<^sub>R j)"
                have "(?a \<bullet> i, ?a \<bullet> j) = p"
                     proof
                       have "(fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i = fst p"
                            apply (simp add: inner_add_left)
                            using Base_vecs by (auto simp add: inner_not_same_Basis)
                       then show "fst ((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = fst p" by auto
                       have "(fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j = snd p"
                            apply (simp add: inner_add_left)
                            using Base_vecs by (auto simp add: inner_not_same_Basis)
                       then show "snd ((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = snd p" by auto
                     qed
                then show "(\<exists>a b. ?a = a *\<^sub>R i + b *\<^sub>R j) \<and> (?a \<bullet> i, ?a \<bullet> j) = p"
                      by auto
             next
               fix x
               assume ass: "(\<exists>a b. x = a *\<^sub>R i + b *\<^sub>R j)\<and> (x \<bullet> i, x \<bullet> j) = p"
               have j_in_Basis_sub_i:
                    "insert j (Basis - {i}) = (Basis -{i})" using Base_vecs by auto
               have i_in_Basis:
                    "insert i (Basis) = Basis" using Base_vecs by auto
               have i_comp: "x \<bullet> i = fst p" using ass by auto
               have j_comp: "x \<bullet> j = snd p" using ass by auto
               have "\<forall>k \<in> Basis. \<not>(k = i) \<and> \<not>(k = j) \<longrightarrow>  x \<bullet> k =0"
                   using Base_vecs
                   by (metis (no_types, lifting) ass inner_left_distrib inner_not_same_Basis inner_scaleR_left inner_zero_right)
               then have "\<And>b. b \<in> (Basis - {i}) - {j} \<Longrightarrow> x \<bullet> b = 0" by auto
               then have "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b) = 0"
                    using Groups_Big.comm_monoid_add_class.sum.neutral by auto
               then have "(\<Sum>b\<in>Basis - {i}. (x \<bullet> b) *\<^sub>R b) = (x \<bullet> j) *\<^sub>R j"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "j"]
                          using Base_vecs by (auto simp add: j_in_Basis_sub_i)
               then have "(\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Base_vecs and
                          Groups_Big.comm_monoid_add_class.sum.insert_remove[of "Basis -{i}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "i"]
                          by (auto simp add: i_in_Basis)
               then have "x = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Euclidean_Space.euclidean_space_class.euclidean_representation[of "x"]
                    by auto
               then show "x = fst p *\<^sub>R i + snd p *\<^sub>R j" by (auto simp add: i_comp j_comp)
             qed
        have 1: "(\<exists>a b. fst p *\<^sub>R i + snd p *\<^sub>R j = a *\<^sub>R i + b *\<^sub>R j)"
             by blast
        have 2: "((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = p"
             using Base_vecs
             by (auto simp add: inner_left_distrib inner_not_same_Basis)
        then show "fst p *\<^sub>R i + snd p *\<^sub>R j = (SOME y. (\<exists>a b. y = a *\<^sub>R i + b *\<^sub>R j) \<and> (y \<bullet> i, y \<bullet> j) = p)"
             using 0 1 2 and
                   Hilbert_Choice.some1_equality[of "(%y. (\<exists>a b. y = a *\<^sub>R i + b *\<^sub>R j) \<and> (y \<bullet> i, y \<bullet> j) = p)"
                                      "fst p *\<^sub>R i + snd p *\<^sub>R j"]
             by auto
      qed

lemma pair_to_euclid_inv_euclid_to_pair_twoD:
      (*This should be pair_to_euclid = inv_into Dy euclid_to_pair *)
      "pair_to_euclid = inv euclid_to_pair"
      apply (auto simp: euclid_to_pair_def pair_to_euclid_def inv_into_def)
      proof
        fix p
        have 0: "\<exists>!x. (x \<bullet> i, x \<bullet> j) = p"
             proof
                let ?a = "(fst p *\<^sub>R i + snd p *\<^sub>R j)"
                have "(?a \<bullet> i, ?a \<bullet> j) = p"
                     proof
                       have "(fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i = fst p"
                            apply (simp add: inner_add_left)
                            using Base_vecs by (auto simp add: inner_not_same_Basis)
                       then show "fst ((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = fst p" by auto
                       have "(fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j = snd p"
                            apply (simp add: inner_add_left)
                            using Base_vecs by (auto simp add: inner_not_same_Basis)
                       then show "snd ((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = snd p" by auto
                     qed
                then show " (?a \<bullet> i, ?a \<bullet> j) = p"
                      by auto
             next
               fix x
               assume ass: "(x \<bullet> i, x \<bullet> j) = p"
               have j_in_Basis_sub_i:
                    "insert j (Basis - {i}) = (Basis -{i})" using Base_vecs by auto
               have i_in_Basis:
                    "insert i (Basis) = Basis" using Base_vecs by auto
               have i_comp: "x \<bullet> i = fst p" using ass by auto
               have j_comp: "x \<bullet> j = snd p" using ass by auto
               have "(Basis - {i}) - {j} = {}"
                   using Base_vecs twoD_space
                   by auto
               then have "\<And>b. b \<in> (Basis - {i}) - {j} \<Longrightarrow> x \<bullet> b = 0" by auto
               then have "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b) = 0"
                    using Groups_Big.comm_monoid_add_class.sum.neutral by auto
               then have "(\<Sum>b\<in>Basis - {i}. (x \<bullet> b) *\<^sub>R b) = (x \<bullet> j) *\<^sub>R j"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "j"]
                          using Base_vecs by (auto simp add: j_in_Basis_sub_i)
               then have "(\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Base_vecs and
                          Groups_Big.comm_monoid_add_class.sum.insert_remove[of "Basis -{i}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "i"]
                          by (auto simp add: i_in_Basis)
               then have "x = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Euclidean_Space.euclidean_space_class.euclidean_representation[of "x"]
                    by auto
               then show "x = fst p *\<^sub>R i + snd p *\<^sub>R j" by (auto simp add: i_comp j_comp)
             qed
        have 1: "(\<exists>a b. fst p *\<^sub>R i + snd p *\<^sub>R j = a *\<^sub>R i + b *\<^sub>R j)"
             by auto
        have 2: "((fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> i, (fst p *\<^sub>R i + snd p *\<^sub>R j) \<bullet> j) = p"
             using Base_vecs
             by (auto simp add: inner_left_distrib inner_not_same_Basis)
        then show "fst p *\<^sub>R i + snd p *\<^sub>R j = (SOME y.  (y \<bullet> i, y \<bullet> j) = p)"
             using 0 1 2 and
                   Hilbert_Choice.some1_equality[of "(%y. (y \<bullet> i, y \<bullet> j) = p)"
                                      "fst p *\<^sub>R i + snd p *\<^sub>R j"]
             by auto
      qed

lemma inj_euclid_to_pair_twoD:
      "inj euclid_to_pair"
      apply (simp add: inj_iff pair_to_euclid_inv_euclid_to_pair_twoD[symmetric])
      apply (simp add: pair_to_euclid_def euclid_to_pair_def id_def o_def)
  proof
    fix x::'a
    show "(x \<bullet> i) *\<^sub>R i + (x \<bullet> j) *\<^sub>R j = x"
         using  euclidean_representation[of "x"] Base_vecs
         by (auto simp add: twoD_space)
  qed

lemma eculid_dist_eq_pait_dist:
      fixes a b c d::"real" and
          x::"'a"
      shows "dist (pair_to_euclid(a, b) + K) (c *\<^sub>R i + d *\<^sub>R j + K)  \<le> dist (a, b) (euclid_to_pair (c *\<^sub>R i + d *\<^sub>R j))"
      apply (simp add: euclid_to_pair_def pair_to_euclid_def dist_Pair_Pair dist_norm norm_Pair)
      proof -
        have "a *\<^sub>R i + b *\<^sub>R j - d *\<^sub>R j - c *\<^sub>R i = (a -c) *\<^sub>R i + (b - d) *\<^sub>R j" by (metis (no_types, lifting) add_diff_eq add_uminus_conv_diff pth_9(1) real_vector.scale_minus_left)
        then show "norm (a *\<^sub>R i + b *\<^sub>R j - (c *\<^sub>R i + d *\<^sub>R j)) \<le> sqrt ((a - (c *\<^sub>R i + d *\<^sub>R j) \<bullet> i)\<^sup>2 + (b - (c *\<^sub>R i + d *\<^sub>R j) \<bullet> j)\<^sup>2)"
             using norm_i_j_sq_ubound[of "((a - c) *\<^sub>R i + (b - d) *\<^sub>R j)"]
             apply (simp only: real_inner_class.inner_add_left)
             using Base_vecs
             by (auto simp add: euclidean_space_class.inner_not_same_Basis Real_Vector_Spaces.scaleR_diff_left[symmetric] diff_add_eq_diff_diff_swap)
      qed

lemma euclid_gauge_to_pair_gauge:
      fixes d
      assumes "gauge d"
      shows "gauge (%p. euclid_to_pair ` d(pair_to_euclid p))"
      apply (simp add: gauge_def)
  proof-
    {
      fix a b:: real
      have "(a,b) \<in> euclid_to_pair ` d (pair_to_euclid (a, b))"
           proof -
             have inv_ok: "euclid_to_pair (pair_to_euclid (a, b)) = (a, b)"
                      apply (simp only: real_inner_class.inner_add_left pair_to_euclid_def euclid_to_pair_def)
                      using euclidean_space_class.inner_same_Basis Base_vecs
                       by (auto simp add: euclidean_space_class.inner_not_same_Basis)
             have "pair_to_euclid(a,b) \<in> d (pair_to_euclid(a,b))"
                  using assms(1)
                  by (auto simp add: gauge_def)
             then show ?thesis
                  using inv_ok by force
           qed
    } note * = this
    {
      fix a b:: real
      have "open (euclid_to_pair ` d (pair_to_euclid (a, b)))"
           proof -
             have "open (d (pair_to_euclid (a, b)))" using assms(1) by (auto simp add: gauge_def)
             then show ?thesis
                  apply (simp add: open_dist)
                  proof -
                    {
                      fix x::'a
                      assume open_euclid_set: "\<And>x. x \<in>d (pair_to_euclid (a, b)) \<Longrightarrow> \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> d (pair_to_euclid (a, b))"
                      assume "x \<in>d (pair_to_euclid (a, b))"
                      then obtain e::real where e_good: "e > 0 \<and> (\<forall>y. dist y x < e \<longrightarrow> y \<in> d (pair_to_euclid (a, b)))" using open_euclid_set by auto
                      have j_in_Basis_sub_i:
                           "insert j (Basis - {i}) = (Basis -{i})" using Base_vecs by auto
                      have i_in_Basis:
                           "insert i (Basis) = Basis" using Base_vecs by auto
                      have "x = ( (x \<bullet> i) *\<^sub>R i + (\<Sum>b\<in>(Basis - {i}). (x \<bullet> b) *\<^sub>R b))"
                           using Base_vecs euclidean_representation[of "x"]
                                 Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis)" "(%b. (x  \<bullet> b) *\<^sub>R b)" "i"]
                           by (simp add: i_in_Basis)
                      then have x_i_j_comps: "x = ( (x \<bullet> i) *\<^sub>R i + (x \<bullet> j) *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b))"
                           using Base_vecs euclidean_representation[of "x"]
                                 Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})" "(%b. (x  \<bullet> b) *\<^sub>R b)" "j"]
                           by (simp add: j_in_Basis_sub_i ab_semigroup_add_class.add_ac(1))
                      {
                        fix a' b'::real
                        assume "dist (a', b') (euclid_to_pair x) < e"
                        then have "dist ((pair_to_euclid(a', b')) + (\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)) (x) < e"
                             using eculid_dist_eq_pait_dist x_i_j_comps Base_vecs
                             apply (simp only: inner_add_left pair_to_euclid_def euclid_to_pair_def )
                             apply (simp add: inner_not_same_Basis)
                             by (smt dist_add_cancel2)
                        then have euclid_in_open_set: "((pair_to_euclid(a', b')) + (\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)) \<in> d (pair_to_euclid (a, b))"
                             using e_good by auto
                        have "(a', b') \<in> euclid_to_pair ` (d (pair_to_euclid (a, b)))"
                             apply (simp add: euclid_to_pair_def image_def)
                             proof -
                               have 0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)  \<bullet> i = 0"
                                    using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "x"] Base_vecs
                                    by auto
                               have 1: "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)  \<bullet> j = 0"
                                    using not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "x"] Base_vecs
                                    by auto
                               have "((pair_to_euclid(a', b')) + (\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)) \<bullet> i = a'
                                     \<and> ((pair_to_euclid(a', b')) + (\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b)) \<bullet> j = b'"
                                    using Base_vecs and 0 and 1
                                    by (auto simp add: inner_add_left pair_to_euclid_def euclid_to_pair_def inner_not_same_Basis)
                               then show "\<exists>x\<in>d (pair_to_euclid (a, b)). a' = x \<bullet> i \<and> b' = x \<bullet> j"
                                    using euclid_in_open_set
                                    by force
                             qed
                      }
                      then have "\<forall>a' b'. dist (a', b') (euclid_to_pair x) < e
                                    \<longrightarrow> (a', b') \<in> euclid_to_pair ` (d (pair_to_euclid (a, b)))" by auto
                      then have "\<exists>e>0. \<forall>a' b'. dist (a', b') (euclid_to_pair x) < e
                                          \<longrightarrow> (a', b') \<in> euclid_to_pair ` (d (pair_to_euclid (a, b)))" using e_good by auto
                    }
                    then show
                          "\<forall>x\<in>d (pair_to_euclid (a, b)). \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> d (pair_to_euclid (a, b)) \<Longrightarrow>
                                  \<forall>x\<in>d (pair_to_euclid (a, b)).
                                             \<exists>e>0. \<forall>a' b'. dist (a', b') (euclid_to_pair x) < e \<longrightarrow> (a', b') \<in> euclid_to_pair ` d (pair_to_euclid (a, b))"
                    by auto
                  qed
           qed
    } note ** = this
    show "\<forall>a b. (a, b) \<in> euclid_to_pair ` d (pair_to_euclid (a, b)) \<and> open (euclid_to_pair ` d (pair_to_euclid (a, b)))"
         using * and ** and gauge_def by auto
  qed

lemma pair_cbox_to_euclid_cbox:
      fixes a b a' b'::real
      shows "pair_to_euclid ` cbox (a, b) (a', b') = cbox (pair_to_euclid(a,b)) (pair_to_euclid(a',b'))"
      apply (auto simp add: image_def cbox_def pair_to_euclid_def real_pair_basis)
      proof -
        fix ia::'a and a'' b'':: real
        assume ia_b'se: "ia \<in> Basis"
        assume a''_ass: "a \<le> a''" "a'' \<le> a'"
        assume b''_ass: "b \<le> b''" "b'' \<le> b'"
        show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
          proof (cases "ia = i")
            assume "ia = i"
            then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                      apply (simp only: real_inner_class.inner_add_left)
                      using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and a''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
          next
            assume ia_neq_i: "\<not>(ia = i)"
            then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                 proof (cases "ia =j")
                   assume "ia = j"
                   then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 next
                   assume "\<not> (ia = j)"
                   then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs and ia_neq_i and ia_b'se
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 qed
           qed
        show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
          proof (cases "ia = i")
            assume "ia = i"
            then show " (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia \<le>  (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                      apply (simp only: real_inner_class.inner_add_left)
                      using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and a''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
          next
            assume ia_neq_i: "\<not>(ia = i)"
            then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                 proof (cases "ia =j")
                   assume "ia = j"
                   then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 next
                   assume "\<not> (ia = j)"
                   then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs and ia_neq_i and ia_b'se
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 qed
          qed
      next
         show "\<And>x. \<forall>ia\<in>Basis. (a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> x \<bullet> ia \<and> x \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia \<Longrightarrow>
                  \<exists>a''\<ge>a. a'' \<le> a' \<and> (\<exists>b''\<ge>b. b'' \<le> b' \<and> x = a'' *\<^sub>R i + b'' *\<^sub>R j)"
             proof -
               fix x
               assume x_bounds:
               "\<forall>ia\<in>Basis. (a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia \<le> x \<bullet> ia \<and> x \<bullet> ia \<le> (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
               then have x_i_j: "x \<bullet> i \<ge> a \<and> x \<bullet> i \<le> a' \<and> x \<bullet> j \<ge> b \<and> x \<bullet> j \<le> b'"
                    apply (simp only: real_inner_class.inner_add_left)
                    using euclidean_space_class.inner_same_Basis and
                          Base_vecs
                     by (auto simp add: euclidean_space_class.inner_not_same_Basis)
               have x_k: "\<And>k. k\<in> Basis \<Longrightarrow> \<not>(k = i) \<Longrightarrow> \<not>(k = j) \<Longrightarrow> x \<bullet> k = 0"
                    proof -
                      fix k::'a
                      assume k_ass: "k\<in> Basis" "\<not>(k = i)" "\<not>(k = j)"
                      have lower_bound_zero:
                           "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> k = 0"
                           using k_ass and Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "i" "k"] and
                                 Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "j" "k"] and Base_vecs
                           by (auto simp add: real_inner_class.inner_add_left)
                      have upper_bound_zero:
                           "(a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> k = 0"
                           using k_ass and Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "i" "k"] and
                                 Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "j" "k"] and Base_vecs
                           by (auto simp add: real_inner_class.inner_add_left)
                       show "x \<bullet> k = 0"
                             using lower_bound_zero and upper_bound_zero and x_bounds and k_ass
                            by auto
                     qed
               have j_in_Basis_sub_i:
                    "insert j (Basis - {i}) = (Basis -{i})" using Base_vecs by auto
               have i_in_Basis:
                    "insert i (Basis) = Basis" using Base_vecs by auto
               have "\<And>b. b \<in> (Basis - {i}) - {j} \<Longrightarrow> x \<bullet> b = 0"
                    proof -
                      fix b::'a
                      assume x_neq_i_j: "b \<in> (Basis - {i}) - {j}"
                      then have b_in_b'sis: "b \<in> Basis" by auto
                      have "\<not>(b = i) \<and> \<not>(b = j)" using x_neq_i_j
                           by auto
                      then show "x \<bullet> b = 0" using x_k and b_in_b'sis by (auto simp add: x_neq_i_j)
                    qed
               then have "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b) = 0"
                    using Groups_Big.comm_monoid_add_class.sum.neutral by auto
               then have "(\<Sum>b\<in>Basis - {i}. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> j) *\<^sub>R j"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "j"]
                          by (auto simp add: j_in_Basis_sub_i)
               then have "(\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Base_vecs and
                          Groups_Big.comm_monoid_add_class.sum.insert_remove[of "Basis -{i}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "i"]
                          by (auto simp add: i_in_Basis)
               then have "x = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using euclidean_representation[of "x"]
                    by auto
               then show "\<exists>a''\<ge>a. a'' \<le> a' \<and> (\<exists>b''\<ge>b. b'' \<le> b' \<and> x = a'' *\<^sub>R i + b'' *\<^sub>R j)" using x_i_j by auto
             qed
      qed

lemma pair_box_to_euclid_box:
      fixes a b a' b'::real
      shows "pair_to_euclid ` box (a, b) (a', b') = box (pair_to_euclid(a,b)) (pair_to_euclid(a',b'))"
      apply (auto simp add: image_def box_def pair_to_euclid_def real_pair_basis)
      proof -
        fix ia::'a and a'' b'':: real
        assume ia_b'se: "ia \<in> Basis"
        assume a''_ass: "a < a''" "a'' < a'"
        assume b''_ass: "b < b''" "b'' < b'"
        show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
          proof (cases "ia = i")
            assume "ia = i"
            then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                      apply (simp only: real_inner_class.inner_add_left)
                      using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and a''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
          next
            assume ia_neq_i: "\<not>(ia = i)"
            then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                 proof (cases "ia =j")
                   assume "ia = j"
                   then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 next
                   assume "\<not> (ia = j)"
                   then show "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs and ia_neq_i and ia_b'se and twoD_space
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 qed
           qed
        show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
          proof (cases "ia = i")
            assume "ia = i"
            then show " (a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia <  (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                      apply (simp only: real_inner_class.inner_add_left)
                      using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and a''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
          next
            assume ia_neq_i: "\<not>(ia = i)"
            then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                 proof (cases "ia =j")
                   assume "ia = j"
                   then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 next
                   assume "\<not> (ia = j)"
                   then show "(a'' *\<^sub>R i + b'' *\<^sub>R j) \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
                        apply (simp only: real_inner_class.inner_add_left)
                        using euclidean_space_class.inner_same_Basis and
                             Base_vecs and ia_neq_i and ia_b'se and twoD_space
                             and b''_ass by (auto simp add: euclidean_space_class.inner_not_same_Basis)
                 qed
          qed
      next
         show "\<And>x. \<forall>ia\<in>Basis. (a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < x \<bullet> ia \<and> x \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia \<Longrightarrow>
                  \<exists>a''>a. a'' < a' \<and> (\<exists>b''>b. b'' < b' \<and> x = a'' *\<^sub>R i + b'' *\<^sub>R j)"
             proof -
               fix x
               assume x_bounds:
               "\<forall>ia\<in>Basis. (a *\<^sub>R i + b *\<^sub>R j) \<bullet> ia < x \<bullet> ia \<and> x \<bullet> ia < (a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> ia"
               then have x_i_j: "x \<bullet> i > a \<and> x \<bullet> i < a' \<and> x \<bullet> j > b \<and> x \<bullet> j < b'"
                    apply (simp only: real_inner_class.inner_add_left)
                    using euclidean_space_class.inner_same_Basis and
                          Base_vecs
                     by (auto simp add: euclidean_space_class.inner_not_same_Basis)
               have x_k: "\<And>k. k\<in> Basis \<Longrightarrow> \<not>(k = i) \<Longrightarrow> \<not>(k = j) \<Longrightarrow> x \<bullet> k = 0"
                    proof -
                      fix k::'a
                      assume k_ass: "k\<in> Basis" "\<not>(k = i)" "\<not>(k = j)"
                      have lower_bound_zero:
                           "(a *\<^sub>R i + b *\<^sub>R j) \<bullet> k = 0"
                           using k_ass and Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "i" "k"] and
                                 Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "j" "k"] and Base_vecs
                           by (auto simp add: real_inner_class.inner_add_left)
                      have upper_bound_zero:
                           "(a' *\<^sub>R i + b' *\<^sub>R j) \<bullet> k = 0"
                           using k_ass and Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "i" "k"] and
                                 Euclidean_Space.euclidean_space_class.inner_not_same_Basis [of "j" "k"] and Base_vecs
                           by (auto simp add: real_inner_class.inner_add_left)
                       show "x \<bullet> k = 0"
                             using lower_bound_zero and upper_bound_zero and x_bounds and k_ass
                            by auto
                     qed
               have j_in_Basis_sub_i:
                    "insert j (Basis - {i}) = (Basis -{i})" using Base_vecs by auto
               have i_in_Basis:
                    "insert i (Basis) = Basis" using Base_vecs by auto
               have "\<And>b. b \<in> (Basis - {i}) - {j} \<Longrightarrow> x \<bullet> b = 0"
                    proof -
                      fix b::'a
                      assume x_neq_i_j: "b \<in> (Basis - {i}) - {j}"
                      then have b_in_b'sis: "b \<in> Basis" by auto
                      have "\<not>(b = i) \<and> \<not>(b = j)" using x_neq_i_j
                           by auto
                      then show "x \<bullet> b = 0" using x_k and b_in_b'sis by (auto simp add: x_neq_i_j)
                    qed
               then have "(\<Sum>b\<in>(Basis - {i}) - {j}. (x \<bullet> b) *\<^sub>R b) = 0"
                    using Groups_Big.comm_monoid_add_class.sum.neutral by auto
               then have "(\<Sum>b\<in>Basis - {i}. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> j) *\<^sub>R j"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "j"]
                          by (auto simp add: j_in_Basis_sub_i)
               then have "(\<Sum>b\<in>Basis. (x \<bullet> b) *\<^sub>R b) = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Base_vecs and
                          Groups_Big.comm_monoid_add_class.sum.insert_remove[of "Basis -{i}" "(%b. (x  \<bullet> b) *\<^sub>R b)" "i"]
                          by (auto simp add: i_in_Basis)
               then have "x = (x  \<bullet> i) *\<^sub>R i + (x  \<bullet> j) *\<^sub>R j"
                    using Euclidean_Space.euclidean_space_class.euclidean_representation[of "x"]
                    by auto
               then show "\<exists>a''>a. a'' < a' \<and> (\<exists>b''>b. b'' < b' \<and> x = a'' *\<^sub>R i + b'' *\<^sub>R j)" using x_i_j by auto
             qed
      qed

lemma euclid_cbox_to_pair_cbox:
      fixes a b::'a
      assumes cbox_nempty: "\<not>(cbox a b = {})"
      shows "euclid_to_pair ` cbox a b = cbox (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
proof (cases "\<forall>k \<in> Basis. a \<bullet> k \<le> b \<bullet> k")
  assume "\<not>(\<forall>k \<in> Basis. a \<bullet> k \<le> b \<bullet> k)"
  then have "cbox a b = {}"
        apply (auto simp add: cbox_def)
        by force
  then show ?thesis using assms by auto
next
  assume no_b'd_k:"(\<forall>k \<in> Basis. a \<bullet> k \<le> b \<bullet> k)"
  show "euclid_to_pair ` cbox a b = cbox (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
      apply (auto simp add: euclid_to_pair_def cbox_def image_def)
      proof -
        fix a' b':: real and x::'a
        assume is_real_basis: "(a', b') \<in> Basis"
        assume x_bounds: "\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
        show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
        show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
      next
        fix a' b':: real
        assume a'_b'_bounds: "\<forall>ia\<in>Basis. (a \<bullet> i, a \<bullet> j) \<bullet> ia \<le> (a', b') \<bullet> ia \<and> (a', b') \<bullet> ia \<le> (b \<bullet> i, b \<bullet> j) \<bullet> ia"
        then have case_i: "a \<bullet> i \<le> a' \<and> a' \<le> b \<bullet> i" by (auto simp add: real_pair_basis)
        have case_j: "a \<bullet> j \<le> b' \<and> b' \<le> b \<bullet> j" using a'_b'_bounds by (auto simp add: real_pair_basis)
        have rest_of_a_i_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> i = 0"
             using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "a"] Base_vecs
             by auto
        have rest_of_a_j_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> j = 0"
             using not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "a"] Base_vecs
             by auto
        have a_k: "\<And>k. \<not>(k = i) \<Longrightarrow>  \<not>(k = j) \<Longrightarrow>(k \<in> Basis) \<Longrightarrow> a \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> k"
             proof -
               fix k::'a
               assume ass1: "\<not>(k = i)"
               assume ass2: "\<not>(k = j)"
               assume ass3: "(k \<in> Basis)"
               have insert_k: "insert k ((Basis - {i}) - {j}) = (Basis - {i}) - {j}" using ass1 and ass2 and ass3 by auto
               have "(\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) = (a \<bullet> k) *\<^sub>R k + (\<Sum>b\<in>((Basis - {i}) - {j})-{k}. (a \<bullet> b) *\<^sub>R b)"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (a  \<bullet> b) *\<^sub>R b)" "k"] Base_vecs
                    by (auto simp add: insert_k)
               then show " a \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> k"
                    using rest_of_a_k_is_0[of "k"] ass3
                    by (auto simp add: real_inner_class.inner_add_left)
             qed
        have 0: "(\<And>k. k\<in>Basis \<Longrightarrow> a \<bullet> k \<le> (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                                  (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<le> b \<bullet> k)"
             proof -
               fix k::'a
               assume k_Basis: "k \<in> Basis"
               show "a \<bullet> k \<le> (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                     (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<le> b \<bullet> k"
                     proof (cases "k = i")
                       assume "k = i"
                       then show ?thesis
                            using case_i and euclidean_space_class.inner_same_Basis and
                                  Base_vecs
                             by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_a_i_is_0)
                     next
                       assume k_neq_i: "\<not>(k = i)"
                       show ?thesis
                            proof (cases "k = j")
                              assume "k = j"
                              then show ?thesis
                                   using case_j and euclidean_space_class.inner_same_Basis and
                                         Base_vecs
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_a_j_is_0)
                            next
                              assume k_neq_j: "\<not>(k = j)"
                              then show ?thesis
                                   using k_Basis and Base_vecs and k_neq_i and k_neq_j and no_b'd_k
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                                real_inner_class.inner_add_left
                                                a_k[ of "k" ] )
                            qed
                     qed
             qed
          have 1: "a' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> i \<and>
                   b' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> j"
                  using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "a"] not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "a"] Base_vecs
                  by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                                real_inner_class.inner_add_left)
          show "\<exists>x. (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and> a' = x \<bullet> i \<and> b' = x \<bullet> j" using 0 and 1 by auto
      qed
qed

lemma euclid_cbox_to_pair_cbox_twoD:
      fixes a b::'a
      shows "euclid_to_pair ` cbox a b = cbox (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
proof -
  show "euclid_to_pair ` cbox a b = cbox (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
      apply (auto simp add: euclid_to_pair_def cbox_def image_def)
      proof -
        fix a' b':: real and x::'a
        assume is_real_basis: "(a', b') \<in> Basis"
        assume x_bounds: "\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
        show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' \<le> x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
        show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' \<le> b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
      next
        fix a' b':: real
        assume a'_b'_bounds: "\<forall>ia\<in>Basis. (a \<bullet> i, a \<bullet> j) \<bullet> ia \<le> (a', b') \<bullet> ia \<and> (a', b') \<bullet> ia \<le> (b \<bullet> i, b \<bullet> j) \<bullet> ia"
        then have case_i: "a \<bullet> i \<le> a' \<and> a' \<le> b \<bullet> i" by (auto simp add: real_pair_basis)
        have case_j: "a \<bullet> j \<le> b' \<and> b' \<le> b \<bullet> j" using a'_b'_bounds by (auto simp add: real_pair_basis)
        have rest_of_a_i_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> i = 0"
             using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "a"] Base_vecs
             by (auto)
        have rest_of_a_j_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> j = 0"
             using not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "a"] Base_vecs
             by (auto)
        have a_k: "\<And>k. \<not>(k = i) \<Longrightarrow>  \<not>(k = j) \<Longrightarrow>(k \<in> Basis) \<Longrightarrow> a \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> k"
                     proof -
               fix k::'a
               assume ass1: "\<not>(k = i)"
               assume ass2: "\<not>(k = j)"
               assume ass3: "(k \<in> Basis)"
               have insert_k: "insert k ((Basis - {i}) - {j}) = (Basis - {i}) - {j}" using ass1 and ass2 and ass3 by auto
               have "(\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) = (a \<bullet> k) *\<^sub>R k + (\<Sum>b\<in>((Basis - {i}) - {j})-{k}. (a \<bullet> b) *\<^sub>R b)"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (a  \<bullet> b) *\<^sub>R b)" "k"] Base_vecs
                    by (auto simp add: insert_k)
               then show " a \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b) \<bullet> k"
                    using rest_of_a_k_is_0[of "k"] ass3
                    by (auto simp add: real_inner_class.inner_add_left)
             qed
        have 0: "(\<And>k. k\<in>Basis \<Longrightarrow> a \<bullet> k \<le> (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                                  (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<le> b \<bullet> k)"
             proof -
               fix k::'a
               assume k_Basis: "k \<in> Basis"
               show "a \<bullet> k \<le> (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                     (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> k \<le> b \<bullet> k"
                     proof (cases "k = i")
                       assume "k = i"
                       then show ?thesis
                            using case_i and euclidean_space_class.inner_same_Basis and
                                  Base_vecs
                             by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_a_i_is_0)
                     next
                       assume k_neq_i: "\<not>(k = i)"
                       show ?thesis
                            proof (cases "k = j")
                              assume "k = j"
                              then show ?thesis
                                   using case_j and euclidean_space_class.inner_same_Basis and
                                         Base_vecs
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_a_j_is_0)
                            next
                              assume k_neq_j: "\<not>(k = j)"
                              then show ?thesis
                                   using k_Basis and Base_vecs and k_neq_i and k_neq_j and twoD_space
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                                real_inner_class.inner_add_left
                                                a_k[ of "k" ] )
                            qed
                     qed
             qed
          have 1: "a' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> i \<and>
                   b' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (a \<bullet> b) *\<^sub>R b)) \<bullet> j"
                  using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "a"] not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "a"] Base_vecs
                  by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                                real_inner_class.inner_add_left)
          show "\<exists>x. (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i) \<and> a' = x \<bullet> i \<and> b' = x \<bullet> j" using 0 and 1 by auto
      qed
qed

lemma euclid_box_to_pair_box:
      fixes a b::'a
      assumes box_nempty: "\<not>(box a b = {})"
      shows "euclid_to_pair ` box a b = box (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
proof (cases "\<forall>k \<in> Basis. a \<bullet> k < b \<bullet> k")
  assume "\<not>(\<forall>k \<in> Basis. a \<bullet> k < b \<bullet> k)"
  then have "box a b = {}"
        apply (auto simp add: box_def)
        by force
  then show ?thesis using assms by auto
next
  assume no_b'd_k:"(\<forall>k \<in> Basis. a \<bullet> k < b \<bullet> k)"
  show "euclid_to_pair ` box a b = box (a \<bullet> i, a \<bullet> j) (b \<bullet> i, b \<bullet> j)"
      apply (auto simp add: euclid_to_pair_def box_def image_def)
      proof -
        fix a' b':: real and x::'a
        assume is_real_basis: "(a', b') \<in> Basis"
        assume x_bounds: "\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i"
        show " a \<bullet> i * a' + a \<bullet> j * b' < x \<bullet> i * a' + x \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' < x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " a \<bullet> i * a' + a \<bullet> j * b' < x \<bullet> i * a' + x \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
        show " x \<bullet> i * a' + x \<bullet> j * b' < b \<bullet> i * a' + b \<bullet> j * b'"
             proof (cases "(a', b') = (0,1)")
               assume "(a', b') = (0,1)"
               then have "a' = 0 \<and> b' = 1" by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' < b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             next
               assume "\<not>((a', b') = (0,1))"
               then have "a' = 1 \<and> b' = 0" using real_pair_basis and is_real_basis by auto
               then show " x \<bullet> i * a' + x \<bullet> j * b' < b \<bullet> i * a' + b \<bullet> j * b'" using x_bounds and Base_vecs by auto
             qed
      next
        fix a' b':: real
        assume a'_b'_bounds: "\<forall>ia\<in>Basis. (a \<bullet> i, a \<bullet> j) \<bullet> ia < (a', b') \<bullet> ia \<and> (a', b') \<bullet> ia < (b \<bullet> i, b \<bullet> j) \<bullet> ia"
        then have case_i: "a \<bullet> i < a' \<and> a' < b \<bullet> i" by (auto simp add: real_pair_basis)
        have case_j: "a \<bullet> j < b' \<and> b' < b \<bullet> j" using a'_b'_bounds by (auto simp add: real_pair_basis)
        obtain c where c_in_box: "c \<in> box a b" using box_nempty by auto
        then have c_is_good: "\<forall>k \<in> Basis. a \<bullet> k < c \<bullet> k \<and> c \<bullet> k < b \<bullet> k" by (auto simp add: box_def)
        have rest_of_c_i_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b) \<bullet> i = 0"
             using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "c"] Base_vecs
             by (auto)
        have rest_of_c_j_is_0: "(\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b) \<bullet> j = 0"
             using not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "c"] Base_vecs
             by (auto)
        have c_k: "\<And>k. \<not>(k = i) \<Longrightarrow>  \<not>(k = j) \<Longrightarrow>(k \<in> Basis) \<Longrightarrow> c \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (c \<bullet> b) *\<^sub>R b) \<bullet> k"
                     proof -
               fix k::'a
               assume ass1: "\<not>(k = i)"
               assume ass2: "\<not>(k = j)"
               assume ass3: "(k \<in> Basis)"
               have insert_k: "insert k ((Basis - {i}) - {j}) = (Basis - {i}) - {j}" using ass1 and ass2 and ass3 by auto
               have "(\<Sum>b\<in>Basis - {i} - {j}. (c \<bullet> b) *\<^sub>R b) = (c \<bullet> k) *\<^sub>R k + (\<Sum>b\<in>((Basis - {i}) - {j})-{k}. (c \<bullet> b) *\<^sub>R b)"
                    using Groups_Big.comm_monoid_add_class.sum.insert_remove[of "(Basis - {i})-{j}" "(%b. (c  \<bullet> b) *\<^sub>R b)" "k"] Base_vecs
                    by (auto simp add: insert_k)
               then show " c \<bullet> k = (\<Sum>b\<in>Basis - {i} - {j}. (c \<bullet> b) *\<^sub>R b) \<bullet> k"
                    using rest_of_a_k_is_0[of "k"] ass3
                    by (auto simp add: real_inner_class.inner_add_left)
             qed
        have 0: "(\<And>k. k\<in>Basis \<Longrightarrow> a \<bullet> k < (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                                  (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> k < b \<bullet> k)"
             proof -
               fix k::'a
               assume k_Basis: "k \<in> Basis"
               show "a \<bullet> k < (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> k \<and>
                     (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>(Basis - {i}) - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> k < b \<bullet> k"
                     proof (cases "k = i")
                       assume "k = i"
                       then show ?thesis
                            using case_i and euclidean_space_class.inner_same_Basis and
                                  Base_vecs and c_is_good
                             by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_c_i_is_0)
                     next
                       assume k_neq_i: "\<not>(k = i)"
                       show ?thesis
                            proof (cases "k = j")
                              assume "k = j"
                              then show ?thesis
                                   using case_j and euclidean_space_class.inner_same_Basis and
                                         Base_vecs
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis real_inner_class.inner_add_left rest_of_c_j_is_0)
                            next
                              assume k_neq_j: "\<not>(k = j)"
                              then show ?thesis
                                   using k_Basis and Base_vecs and k_neq_i and k_neq_j and c_is_good
                                   by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                                real_inner_class.inner_add_left
                                                c_k[ of "k"])
                            qed
                     qed
             qed
          have 1: "a' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> i \<and>
                   b' = (a' *\<^sub>R i + b' *\<^sub>R j + (\<Sum>b\<in>Basis - {i} - {j}. (c \<bullet> b) *\<^sub>R b)) \<bullet> j"
               using not_in_sum_zero[of "i" "(Basis - {i}) - {j}" "c"] not_in_sum_zero[of "j" "(Basis - {i}) - {j}" "c"] Base_vecs
               by (auto simp add: euclidean_space_class.inner_not_same_Basis
                                            real_inner_class.inner_add_left)
          show "\<exists>x. (\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i) \<and> a' = x \<bullet> i \<and> b' = x \<bullet> j" using 0 and 1 by auto
      qed
qed

lemma pair_tagged_partial_division_to_euclid_tagged_partial_division_twoD:
      fixes pair_p::"((real * real) * ((real*real) set)) set"
      assumes "pair_p tagged_partial_division_of cbox (x1, y1) (x2, y2)"
      shows "(%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p))) ` pair_p
                      tagged_partial_division_of
                             pair_to_euclid ` cbox (x1, y1) (x2, y2)"
      apply (simp add: tagged_partial_division_of_def)
      proof
        show "finite ((\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p)"
             using assms
             by auto
        next
          {
            fix x k
            assume in_euclid_partial_div: "(x, k) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p"
            then have 0: "x \<in> k"
                 using assms
                 by (auto simp add: tagged_partial_division_of_def pair_to_euclid_def euclid_to_pair_def
                                    image_def)
            have 1: "k \<subseteq> pair_to_euclid ` cbox (x1, y1) (x2, y2) \<and> (\<exists>a b. k = cbox a b)"
                 using in_euclid_partial_div and assms
                 apply (auto simp add: tagged_partial_division_of_def pair_to_euclid_def euclid_to_pair_def
                                    image_def)
                 apply (metis (no_types, lifting) fst_conv snd_conv subsetCE)
                 by (smt Pair_inject image_def in_euclid_partial_div mem_Collect_eq pair_cbox_to_euclid_cbox prod.collapse)
            have "x \<in> k \<and> k \<subseteq> pair_to_euclid ` cbox (x1, y1) (x2, y2) \<and> (\<exists>a b. k = cbox a b)"
                 using 0 and 1 by auto
          }
          then have goal1:
               "(\<forall>x k. (x, k) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<longrightarrow>
                       x \<in> k \<and> k \<subseteq> pair_to_euclid ` cbox (x1, y1) (x2, y2) \<and> (\<exists>a b. k = cbox a b))" by auto
          {
            fix euclid_tag euclid_inter  euclid_tag2 euclid_inter2
            assume ass1: "(euclid_tag, euclid_inter) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p"
            assume ass2: "(euclid_tag2, euclid_inter2) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p"
            assume ass3: "(euclid_tag = euclid_tag2 \<longrightarrow> euclid_inter \<noteq> euclid_inter2)"
            obtain pair_tag where "euclid_tag = pair_to_euclid pair_tag"
                   using ass1
                   by (auto)
            then obtain pair_inter where euclid_inter_is_pair: "(euclid_inter = pair_to_euclid ` pair_inter) \<and> ((pair_tag, pair_inter) \<in> pair_p)"
                   using ass1
                   apply (auto simp add: image_def)
                   by (metis (no_types, lifting) injD inj_pair_to_euclid)
            then obtain pair_inter_x1 pair_inter_x2 pair_inter_y1 pair_inter_y2
                 where pair_inter_cbox: "pair_inter = cbox (pair_inter_x1, pair_inter_y1) (pair_inter_x2, pair_inter_y2)"
                 using tagged_partial_division_ofD(4) and assms
                 by auto
            then have euclid_inter_cbox: "euclid_inter = cbox (pair_to_euclid (pair_inter_x1, pair_inter_y1)) (pair_to_euclid (pair_inter_x2, pair_inter_y2))"
                 using euclid_inter_is_pair
                 by (simp add: pair_cbox_to_euclid_cbox)
            obtain pair_tag2 where "euclid_tag2 = pair_to_euclid pair_tag2"
                   using ass2
                   by (auto)
            then obtain pair_inter2 where euclid_inter_is_pair2: "(euclid_inter2 = pair_to_euclid ` pair_inter2) \<and> ((pair_tag2, pair_inter2) \<in> pair_p)"
                   using ass2
                   apply (auto simp add: image_def)
                   by (metis (no_types, lifting) injD inj_pair_to_euclid)
            then obtain pair_inter2_x1 pair_inter2_x2 pair_inter2_y1 pair_inter2_y2
                 where pair_inter2_cbox: "pair_inter2 = cbox (pair_inter2_x1, pair_inter2_y1) (pair_inter2_x2, pair_inter2_y2)"
                 using tagged_partial_division_ofD(4) and assms
                 by auto
            then have euclid_inter2_cbox: "euclid_inter2 = cbox (pair_to_euclid (pair_inter2_x1, pair_inter2_y1)) (pair_to_euclid (pair_inter2_x2, pair_inter2_y2))"
                 using euclid_inter_is_pair2
                 by (simp add: pair_cbox_to_euclid_cbox)
            have "\<And>pair_tag pair_inter pair_tag2 pair_inter2.
                      (pair_tag, pair_inter) \<in> pair_p \<Longrightarrow>  (pair_tag2, pair_inter2) \<in> pair_p
                      \<Longrightarrow> (pair_tag = pair_tag2 \<longrightarrow> pair_inter \<noteq> pair_inter2)
                      \<Longrightarrow> interior pair_inter \<inter> interior pair_inter2 = {}"
                 using tagged_partial_division_ofD(5) assms
                 by auto
            then have "box (pair_inter_x1, pair_inter_y1)  (pair_inter_x2, pair_inter_y2)
                          \<inter> box (pair_inter2_x1, pair_inter2_y1)  (pair_inter2_x2, pair_inter2_y2) = {}"
                 using euclid_inter_cbox euclid_inter2_cbox euclid_cbox_to_pair_cbox_twoD pair_box_to_euclid_box
                 apply (simp only: pair_to_euclid_def euclid_to_pair_def interior_cbox pair_box_to_euclid_box[symmetric])
                 by (metis (no_types, lifting) \<open>\<And>pair_tag2 pair_tag pair_inter2 pair_inter. \<lbrakk>(pair_tag, pair_inter) \<in> pair_p; (pair_tag2, pair_inter2) \<in> pair_p; pair_tag = pair_tag2 \<longrightarrow> pair_inter \<noteq> pair_inter2\<rbrakk> \<Longrightarrow> interior pair_inter \<inter> interior pair_inter2 = {}\<close> \<open>euclid_tag = pair_to_euclid pair_tag\<close> \<open>euclid_tag2 = pair_to_euclid pair_tag2\<close> ass3 euclid_inter_is_pair euclid_inter_is_pair2 interior_cbox pair_inter2_cbox pair_inter_cbox)
            then have "interior euclid_inter \<inter> interior euclid_inter2 = {}"
                 using euclid_inter_cbox euclid_inter2_cbox euclid_cbox_to_pair_cbox_twoD pair_box_to_euclid_box
                 apply (simp only: interior_cbox pair_box_to_euclid_box[symmetric])
                 by (metis (no_types, lifting) inj_pair_to_euclid image_is_empty image_Int)
          }
          then have goal2:
               "(\<forall>x1 k1 x2 k2.
                               (x1, k1) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<and>
                               (x2, k2) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<and> (x1 = x2 \<longrightarrow> k1 \<noteq> k2) \<longrightarrow>
                               interior k1 \<inter> interior k2 = {})" by blast
          show "(\<forall>x k. (x, k) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<longrightarrow>
                       x \<in> k \<and> k \<subseteq> pair_to_euclid ` cbox (x1, y1) (x2, y2) \<and> (\<exists>a b. k = cbox a b)) \<and>
                (\<forall>x1 k1 x2 k2.
                               (x1, k1) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<and>
                               (x2, k2) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p \<and> (x1 = x2 \<longrightarrow> k1 \<noteq> k2) \<longrightarrow>
                               interior k1 \<inter> interior k2 = {})"
                using goal1 and goal2
                by auto
      qed

lemma pair_tagged_division_to_euclid_tagged_division_twoD:
      fixes pair_p::"((real * real) * ((real*real) set)) set"
      assumes "pair_p tagged_division_of cbox (x1, y1) (x2, y2)"
      shows "(%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p))) ` pair_p
                      tagged_division_of
                             pair_to_euclid ` cbox (x1, y1) (x2, y2)"
  apply(simp add: tagged_division_of_def)
  proof
    show " (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p tagged_partial_division_of pair_to_euclid ` cbox (x1, y1) (x2, y2)"
         using pair_tagged_partial_division_to_euclid_tagged_partial_division_twoD and
               assms
         by (auto simp add: tagged_division_of_def)
    next
       show "\<Union>{k. \<exists>x. (x, k) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p} = pair_to_euclid ` cbox (x1, y1) (x2, y2)"
            apply auto
            proof -
              fix ba::"(real*real) set"
              fix  a b a' b'::real
              assume ass1: "((a, b), ba) \<in> pair_p"
              assume ass2: "(a', b') \<in> ba"
              have x1_le: "x1 \<le> a'"
                   using tagged_division_ofD(3) ass1 ass2 assms
                   by (auto simp add: cbox_def real_pair_basis subset_iff)
              have x2_ge: "a' \<le> x2"
                   using tagged_division_ofD(3) ass1 ass2 assms
                   by (auto simp add: cbox_def real_pair_basis subset_iff)
              have y1_le: "y1 \<le> b'"
                   using tagged_division_ofD(3) ass1 ass2 assms
                   by (auto simp add: cbox_def real_pair_basis subset_iff)
              have y2_ge: "b' \<le> y2"
                   using tagged_division_ofD(3) ass1 ass2 assms
                   by (auto simp add: cbox_def real_pair_basis subset_iff)
              show " pair_to_euclid (a', b') \<in> pair_to_euclid ` cbox (x1, y1) (x2, y2)"
                   using x1_le x2_ge y1_le y2_ge
                   by (auto simp add: pair_cbox_to_euclid_cbox cbox_def image_def pair_to_euclid_def real_pair_basis)
            next
              fix a b::real
              assume x1_le: "x1 \<le> a"
              assume x2_ge: "a \<le> x2"
              assume y1_le: "y1 \<le> b"
              assume y2_ge: "b \<le> y2"
              have a_b_in_cbox: "(a,b) \<in> cbox (x1, y1) (x2, y2)"
                   using x1_le x2_ge y1_le y2_ge
                   by (auto simp add: cbox_def real_pair_basis)
              have "\<exists>(p,pset) \<in> pair_p. (a,b) \<in> pset"
                   using assms and tagged_division_ofD(6)[of "pair_p" "cbox (x1, y1) (x2, y2)"] a_b_in_cbox
                   apply(auto intro: simp add: cbox_def Union_eq real_pair_basis )
                     proof -
                       assume "pair_p tagged_division_of {x. x1 \<le> x \<bullet> (1, 0) \<and> x \<bullet> (1, 0) \<le> x2 \<and> y1 \<le> x \<bullet> (0, 1) \<and> x \<bullet> (0, 1) \<le> y2}"
                       assume "{x. \<exists>xa. (\<exists>a b. ((a, b), xa) \<in> pair_p) \<and> x \<in> xa} = {x. x1 \<le> x \<bullet> (1, 0) \<and> x \<bullet> (1, 0) \<le> x2 \<and> y1 \<le> x \<bullet> (0, 1) \<and> x \<bullet> (0, 1) \<le> y2}"
                       then have "{p. \<exists>r. (\<exists>ra rb. ((ra, rb), r) \<in> pair_p) \<and> p \<in> r} \<in> Collect (op \<in> (a, b))"
                         using a_b_in_cbox by auto
                       then show "\<exists>p\<in>pair_p. case p of (p, r) \<Rightarrow> (a, b) \<in> r"
                       by blast
                     qed
              then obtain p pset where p_p_set_good: "(p,pset) \<in> pair_p \<and> (a,b) \<in> pset" by auto
              then have 0: "pair_to_euclid (a, b) \<in> pair_to_euclid ` pset"
                            apply (auto simp add: pair_to_euclid_def euclid_to_pair_def image_def)
                            by force
              have 1: "(pair_to_euclid p, pair_to_euclid ` pset) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p"
                   using p_p_set_good
                   apply (auto intro: p_p_set_good simp add: pair_to_euclid_def euclid_to_pair_def image_def)
                   by force
              show "\<exists>x. (\<exists>xa. (xa, x) \<in> (\<lambda>p. (pair_to_euclid (fst p), pair_to_euclid ` snd p)) ` pair_p) \<and> pair_to_euclid (a, b) \<in> x"
                   using 0 and 1
                   by auto
            qed
  qed


lemma pair_fine_to_euclid_fine:
      fixes d::"'a \<Rightarrow> 'a set" and
            pair_p::"((real*real) * ((real*real) set)) set"
      assumes "(%p. euclid_to_pair ` d(pair_to_euclid p)) fine pair_p"
      shows "d fine ((%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p))) ` pair_p)"
      using assms
      apply (simp add: fine_def)
  proof
    fix x
    assume ass1: "\<forall>(x, k)\<in>pair_p. k \<subseteq> euclid_to_pair ` d (pair_to_euclid x)"
    assume ass2: "x \<in> pair_p"
    then have "snd x \<subseteq> (euclid_to_pair ` d (pair_to_euclid (fst x)))"
         using ass1
         by (simp add: case_prod_unfold)
    then have "pair_to_euclid ` (snd x) \<subseteq> pair_to_euclid ` (euclid_to_pair ` d (pair_to_euclid (fst x)))"
         by auto
    then show "pair_to_euclid ` snd x \<subseteq> d (pair_to_euclid (fst x))"
         using inj_euclid_to_pair_twoD image_inv_f_f[of "euclid_to_pair"]
               pair_to_euclid_inv_euclid_to_pair_twoD
         by (simp)
  qed

lemma pair_content_eq_euclid_content_twoD:
      fixes s_pair
      shows "content (pair_to_euclid ` (cbox (x1, y1) (x2, y2))) = content (cbox (x1, y1) (x2, y2))"
proof cases
      assume empty_ass: "(cbox (x1, y1) (x2, y2)) = {}"
      then have "(pair_to_euclid ` (cbox (x1, y1) (x2, y2))) = {}" by auto
      then show "content (pair_to_euclid ` cbox (x1, y1) (x2, y2)) = content (cbox (x1, y1) (x2, y2))" using empty_ass by auto
    next
      assume nempty_ass: "cbox (x1, y1) (x2, y2) \<noteq> {}"
      then have i: "(\<forall>i\<in>Basis. (x1,y1) \<bullet> i \<le> (x2,y2) \<bullet> i)" using box_ne_empty(1) by auto
      have "(pair_to_euclid ` cbox (x1, y1) (x2, y2)) \<noteq> {}" using nempty_ass by auto
      then have nempty_ass2: "( (cbox (pair_to_euclid(x1, y1)) (pair_to_euclid (x2, y2)))) \<noteq> {}" using pair_cbox_to_euclid_cbox by auto
      then have ii: "(\<forall>i\<in>Basis. pair_to_euclid(x1,y1) \<bullet> i \<le> pair_to_euclid (x2,y2) \<bullet> i)"
           using box_ne_empty(1)
                 pair_to_euclid_def
           by auto
      show "content (pair_to_euclid ` cbox (x1, y1) (x2, y2)) = content (cbox (x1, y1) (x2, y2))"
           apply (simp add: nempty_ass2 nempty_ass content_cbox' pair_cbox_to_euclid_cbox)
           apply (simp add: twoD_space Base_vecs real_pair_basis euclid_cbox_to_pair_cbox
                       pair_cbox_to_euclid_cbox)
           apply (auto simp add: pair_to_euclid_def euclid_to_pair_def cbox_def inner_add_left inner_not_same_Basis Base_vecs
                                 real_pair_basis twoD_space)
           using Base_vecs(1) Base_vecs(2) Base_vecs(3) inner_not_same_Basis by blast
qed

lemma has_integral_compact_interval_euclid_to_pair:
      fixes a b a' b' K and
            F::"('a \<Rightarrow> real)"
      assumes euclid_integral:
                     "(sum (\<lambda>(x, k). content k *\<^sub>R F x) \<longlongrightarrow> I) (division_filter (pair_to_euclid ` (cbox (a, b) (a', b'))))"
      shows "(sum (\<lambda>(x, k). content k *\<^sub>R F (pair_to_euclid x)) \<longlongrightarrow> I) (division_filter ((cbox (a, b) (a', b'))))"
proof -
  have assum_unfolded: "(\<forall>e2>0. \<exists>d2. gauge d2 \<and>
          (\<forall>p. p tagged_division_of {y. \<exists>x\<in>cbox (a, b) (a', b'). y = pair_to_euclid x} \<and> d2 fine p \<longrightarrow>
            \<bar>(\<Sum>x\<in>p. case x of (x, k) \<Rightarrow> content k * F x) - I\<bar> < e2)) "
       using euclid_integral
       by (auto simp add: tendsto_iff dist_real_def eventually_division_filter image_def)
  {
    fix e::"real" and d::"('a \<Rightarrow> 'a set)"
    assume euclid_gauge: "gauge d"
    assume euclid_integral_expanded:
           "(\<forall>p. p tagged_division_of {y. \<exists>x\<in>cbox (a, b) (a', b'). y = pair_to_euclid x} \<and> d fine p \<longrightarrow>
                \<bar>(\<Sum>x\<in>p. case x of (x, k) \<Rightarrow> content k * F x) - I\<bar> < e)"
    assume e_nzero: "0 < e"
    let ?pair_gauge = " (%p. euclid_to_pair ` d(pair_to_euclid p))"
    {
      fix pair_p
      assume tagged_div: "pair_p tagged_division_of cbox (a, b) (a', b')"
      assume fine: "?pair_gauge fine pair_p"
      let ?euclid_partition = "(%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p))) ` pair_p"
      have euclid_tagged_division:
           "?euclid_partition
                    tagged_division_of {y. \<exists>x\<in>cbox (a, b) (a', b'). y = pair_to_euclid x}"
           using pair_tagged_division_to_euclid_tagged_division_twoD[of "pair_p" "a" "b" "a'" "b'"] and tagged_div
           by (auto simp add: image_def)
      have euclid_fine:"d fine ?euclid_partition"
           using pair_fine_to_euclid_fine and fine
           by auto
      have assum: "\<And>x_pair k_pair. (x_pair,k_pair)\<in>pair_p
                             \<Longrightarrow> \<exists>a b. k_pair = cbox a b"
           using tagged_div tagged_division_ofD(4)
           by blast
      have euclid_sum_error:
           "\<bar>(\<Sum>x\<in>?euclid_partition. case x of (x, k) \<Rightarrow> content k * F x) - I\<bar> < e"
           using euclid_integral_expanded and euclid_fine and euclid_tagged_division by auto
      have "inj_on (%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p))) pair_p"
           using inj_pair_to_euclid_on_pairs inj_on_pairs inj_on_inj_on_image
           by (metis (no_types))
      then have "(\<Sum>(x_pair,k_pair)\<in>pair_p.  content k_pair * F (pair_to_euclid x_pair))
                              = (\<Sum>(x, k)\<in>?euclid_partition. content k * F x)"
           using sum.reindex
                 [of "(%p. (pair_to_euclid (fst p), pair_to_euclid ` (snd p)))"
                     "pair_p"
                     "(%(x,k). content k * F(x))"] and
                 pair_content_eq_euclid_content_twoD and
                 assum
           apply auto
           by (smt case_prod_unfold fst_conv prod.exhaust_sel sum.reindex_cong snd_conv)
      then have "\<bar>(\<Sum>x\<in>pair_p. case x of (x, k) \<Rightarrow> content k * F (pair_to_euclid x)) - I\<bar> < e"
           using euclid_sum_error by linarith
       (* The prrof should be transforming the pair partition into a euclid partition and instantiating
         euclid_integral_expanded with it*)
     }
     then have
               "(\<forall>p. p tagged_division_of cbox (a, b) (a', b') \<and> ?pair_gauge fine p \<longrightarrow>
                 \<bar>(\<Sum>x\<in>p. case x of (x, k) \<Rightarrow> content k * F (pair_to_euclid x)) - I\<bar> < e)" by auto
     then have
              " \<exists>d. gauge d \<and>
                    (\<forall>p. p tagged_division_of cbox (a, b) (a', b') \<and> d fine p \<longrightarrow>
                           \<bar>(\<Sum>x\<in>p. case x of (x, k) \<Rightarrow> content k * F (pair_to_euclid x)) - I\<bar> < e)"
          using euclid_gauge_to_pair_gauge and euclid_gauge by auto
     then have "eventually (\<lambda>p. \<bar>(\<Sum>x\<in>p. case x of (x, k) \<Rightarrow> content k * F (pair_to_euclid x)) - I\<bar> < e) (division_filter (cbox (a, b) (a', b')))"
              using eventually_division_filter
              by auto
   }
  then show "(sum (\<lambda>(x, k). content k *\<^sub>R F (pair_to_euclid x)) \<longlongrightarrow> I) (division_filter (cbox (a, b) (a', b')))"
            using assum_unfolded tendsto_iff
            by (auto simp add: tendsto_iff dist_real_def)
qed

lemma pair_ball_is_euclid_ball_twoD:
      fixes B:: real
      assumes "B > 0"
      shows "\<exists>B'. ball 0 B \<subseteq> pair_to_euclid ` (ball 0 B') \<and> B' \<ge> B"
   proof
     let ?B' = "max B ((SUP x:(euclid_to_pair ` (ball 0 B)). dist 0 x ) + 1)"
     have "\<And>x::'a. x \<in> ball 0 B \<Longrightarrow>  (dist 0 (euclid_to_pair x) < ?B')"
          proof -
            fix x::'a
            have n_empty_ball: "\<not>(ball 0 B = {})" using  ball_eq_empty[of "0" "B"] and assms(1) by auto
            assume "x \<in> ball 0 B"
            then have "(euclid_to_pair x) \<in> (euclid_to_pair ` (ball 0 B))" by auto
            then have "(dist 0 (euclid_to_pair x)) \<le> Sup (dist 0 ` (euclid_to_pair ` ball 0 B))"
                 using bounded_euclid_set_imp_bounded_pair_set[of "ball 0 B"]
                       n_empty_ball
                       image_is_empty
                       bounded_ball[of "0" "B"]
                       bounded_dist_img_bounded
                       bounded_has_Sup(1)[of "dist 0 ` (euclid_to_pair ` (ball 0 B))"]
                  by force
            then show " dist 0 (euclid_to_pair x) < ?B'" by auto
         qed
     then have "euclid_to_pair ` (ball 0 B) \<subseteq> ball 0 ?B'" by auto
     then have 0: "ball 0 B \<subseteq> pair_to_euclid ` ball 0 ?B'"
          using inj_euclid_to_pair_twoD image_inv_f_f[of "euclid_to_pair" "ball 0 B"]
                pair_to_euclid_inv_euclid_to_pair_twoD
          by force
     have 1: "B \<le> ?B'" by auto
     have "ball 0 B \<subseteq> pair_to_euclid ` (ball 0 ?B') \<and> B \<le> ?B'" using 0 and 1 by auto
     then show "ball 0 B \<subseteq> pair_to_euclid ` (ball 0 ?B') \<and> B \<le> ?B'" by auto
   qed

lemma pair_to_euclid_zero:
      shows "pair_to_euclid 0 = 0"
      apply (auto simp: pair_to_euclid_def)
      done

abbreviation has_integral_compact_interval
  where "has_integral_compact_interval f K s \<equiv> (sum (\<lambda>(x, k). content k *\<^sub>R f x) \<longlongrightarrow> K) (division_filter s)"

lemma euclid_integral_to_real_pair:
      fixes D_pair::"(real*real) set"
      assumes "(F_b' has_integral K) (pair_to_euclid ` D_pair)"
      shows "(F_b' o pair_to_euclid  has_integral K) D_pair"
   proof -
     let ?D = "(pair_to_euclid ` D_pair)"
     show "(F_b' o pair_to_euclid has_integral K) D_pair"
     proof (cases "?D = {}")
       assume nempty_D: "\<not>(?D = {})"
       have if_always_true: "\<And> a b a' b'. \<exists>p1 p2. pair_to_euclid ` cbox (a, b) (a', b') = cbox p1 p2"
            using pair_cbox_to_euclid_cbox
            by auto
       {fix K
          {  fix a b a' b'
             have "if \<exists>a2 b2. (pair_to_euclid ` cbox (a, b) (a', b')) = cbox a2 b2 then (sum (\<lambda>(x, k). content k *\<^sub>R F_b' x) \<longlongrightarrow> K) (division_filter (pair_to_euclid ` cbox (a, b) (a', b')))
                             else \<forall>e>0. \<exists>B>0. \<forall>a2 b2. ball 0 B \<subseteq> cbox a2 b2 \<longrightarrow>
                           (\<exists>z. (sum (\<lambda>(x, k). content k *\<^sub>R (if x \<in> pair_to_euclid ` cbox (a, b) (a', b') then F_b' x else 0)) \<longlongrightarrow> z) (division_filter (cbox a2 b2)) \<and>
                                norm (z - K) < e) \<Longrightarrow>
                   D_pair = cbox (a, b) (a', b') \<Longrightarrow>
                       (sum (\<lambda>(x, k). content k *\<^sub>R F_b' (pair_to_euclid x)) \<longlongrightarrow> K) (division_filter (cbox (a, b) (a', b')))"
             using has_integral_compact_interval_euclid_to_pair and
                   if_always_true by (auto simp add: image_def)
         } note * = this
         {
            fix e::"real"
            assume ass1:
                  "if \<exists>a b. ?D = cbox a b
                   then (sum (\<lambda>(x, k). content k *\<^sub>R F_b' x) \<longlongrightarrow> K) (division_filter ?D)
                   else \<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                                          (\<exists>z. (sum (\<lambda>(x, k). content k *\<^sub>R (\<lambda>x. if x \<in> ?D then F_b' x else 0) x) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
                                               norm (z - K) < e)"
            assume ass2: "\<forall>a b a' b'. D_pair \<noteq> cbox (a, b) (a', b')"
            assume ass3: "0 < e"
            {
              assume euclid_integral:
                     "\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                                              (\<exists>z. (sum (\<lambda>(x, k). content k *\<^sub>R (\<lambda>x. if x \<in> ?D then F_b' x else 0) x) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
                                               norm (z - K) < e)"
              then obtain B where b_properties:
                      "B > 0 \<and>
                       (\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                                              (\<exists>z. (sum (\<lambda>(x, k). content k *\<^sub>R (\<lambda>x. if x \<in> ?D then F_b' x else 0) x) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
                                               norm (z - K) < e))" using ass3 by blast
              then have B_more_0: "B > 0" by auto
              then obtain B' where pair_B_props:
                   "ball 0 B \<subseteq> pair_to_euclid ` (ball 0 B') \<and> B' > 0"
                   using pair_ball_is_euclid_ball_twoD
                   by force
              {
                fix a b a' b' ::real
                assume ball_subset: "ball 0 B' \<subseteq> cbox (a, b) (a', b')"
                have eq_funs: "(\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0)
                           = (\<lambda>a. if pair_to_euclid a \<in> pair_to_euclid ` D_pair then F_b' (pair_to_euclid a) else 0)"
                     using inj_pair_to_euclid and Fun.inj_image_mem_iff[of ] by (metis (no_types))
                obtain a1 and a2 where a1_a2_def:
                       "pair_to_euclid ` (cbox (a, b) (a', b')) = cbox a1 a2" using if_always_true by blast
                then have "ball 0 B \<subseteq> cbox a1 a2"
                     proof -
                       have "pair_to_euclid ` ball 0 B' \<subseteq> cbox a1 a2"
                            using a1_a2_def ball_subset by blast
                       then show ?thesis
                            using pair_B_props by blast
                     qed
                then obtain z' where "has_integral_compact_interval (\<lambda>x. if x \<in> ?D then F_b' x else 0) z' (cbox a1 a2) \<and>
                                             norm (z' - K) < e" using b_properties by blast
                then have "has_integral_compact_interval (\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0) z'
                                     (cbox (a, b) (a', b')) \<and>
                           norm(z' - K) < e"
                     using a1_a2_def and eq_funs and
                           has_integral_compact_interval_euclid_to_pair
                               [of "(\<lambda>x. if x \<in> ?D then F_b' x else 0)" "z'" "a" "b" "a'" "b'"]
                     apply (auto simp add: image_def)
                     by metis
                then have "(\<exists>z. has_integral_compact_interval (\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0) z
                                     (cbox (a, b) (a', b')) \<and>
                             norm(z - K) < e)" by blast
              }
              then have "\<forall>a b a' b'.
                         ball 0 B' \<subseteq> cbox (a, b) (a', b') \<longrightarrow>
                          (\<exists>z. has_integral_compact_interval (\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0) z
                               (cbox (a, b) (a', b')) \<and>
                               \<bar>z - K\<bar> < e)" by auto
              then have "\<exists>B>0.
                       \<forall>a b a' b'.
                          ball 0 B \<subseteq> cbox (a, b) (a', b') \<longrightarrow>
                          (\<exists>z. has_integral_compact_interval (\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0) z
                               (cbox (a, b) (a', b')) \<and>
                               \<bar>z - K\<bar> < e)" using pair_B_props by auto
            } note case2_2 = this
                    (*by (auto simp add: has_integral_compact_interval_def)*)
          have D_pair_eq_euclid_cbox: "euclid_to_pair ` ?D = D_pair"
               using surj_euclid_to_pair image_f_inv_f[of "euclid_to_pair"]
               by (simp only: pair_to_euclid_inv_euclid_to_pair_twoD)
          then have if_always_false: "\<And>a b. \<not>(cbox a b = {}) \<Longrightarrow> ?D = cbox a b
                                   \<Longrightarrow> \<exists>l m n k. D_pair = cbox (l, m) (n, k)"
               using euclid_cbox_to_pair_cbox by metis
           have
             "\<exists>B>0. \<forall>a b a' b'.
                      ball 0 B \<subseteq> cbox (a, b) (a', b') \<longrightarrow>
                      (\<exists>z. has_integral_compact_interval (\<lambda>x. if x \<in> D_pair then F_b' (pair_to_euclid x) else 0) z
                            (cbox (a, b) (a', b')) \<and>
                           \<bar>z - K\<bar> < e)"
            proof (cases "\<exists>a b. ?D = cbox a b")
              assume there_is_cbox: "\<exists>a b. ?D = cbox a b"
              then have "\<exists>l m n k. D_pair = cbox (l, m) (n, k)" using if_always_false and there_is_cbox and nempty_D by blast
              then show ?thesis using ass2 by auto
            next
              assume "\<not>(\<exists>a b. ?D = cbox a b)"
              then show ?thesis using case2_2 and ass1 and ass2 and ass3 and image_def by auto
            qed
         } note ** = this
         have D_def: "?D = {y. \<exists>x\<in>D_pair. y = pair_to_euclid x}" using image_def by auto
         then have D_def2: "(pair_to_euclid ` D_pair) = {y. \<exists>x\<in>D_pair. y = pair_to_euclid x}" by auto
         have "(F_b' has_integral K) ?D \<Longrightarrow> ((%a. F_b'(pair_to_euclid a)) has_integral K) D_pair"
              using * ** apply (auto simp add: has_integral_def D_def)
              using D_def2 apply presburger
              using image_def
              by (simp only: D_def2)
        }
        then show ?thesis using assms by (metis (mono_tags, lifting) comp_def has_integral_eq)
     next
       assume empty_D: "(?D = {})"
       then have empty_D_pair: "D_pair = {}" by auto
       then have "K = 0"  using assms and empty_D by (metis has_integral_empty_eq)
       then show ?thesis
            apply( simp only: empty_D_pair)
            by (metis has_integral_empty_eq)
     qed
 qed

end
end
