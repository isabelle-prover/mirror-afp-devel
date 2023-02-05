theory Sharing_Lemmas
  imports
    Additive_Sharing
begin


lemma share_nat_2party_uniform:
  "p \<noteq> q \<Longrightarrow> map_spmf (\<lambda>s. (get_party p s, get_party q s)) (share_nat x) = spmf_of_set UNIV"
proof -
  assume pq: "p\<noteq>q"
  obtain r where r: "q\<noteq>r" "r\<noteq>p" 
    using role_otherE .
  show "map_spmf (\<lambda>s. (get_party p s, get_party q s)) (share_nat x) = spmf_of_set UNIV"
    apply (unfold share_nat_def_calc'[OF pq r, simplified])
    apply (unfold case_prod_unfold)
    apply (fold map_spmf_conv_bind_spmf)
    apply (unfold spmf.map_comp comp_def)
    apply (unfold make_sharing'_sel[OF pq r])
    apply (auto simp: pair_spmf_of_set)
    done
qed

lemma share_nat_party_uniform:
  "map_spmf (get_party p) (share_nat x) = spmf_of_set UNIV"
  supply [simp] = spmf.map_comp comp_def
  apply (unfold share_nat_2party_uniform[of p "next_role p", THEN arg_cong[where f="map_spmf fst"], simplified])
  apply (fold UNIV_Times_UNIV)
  apply (fold pair_spmf_of_set)
  apply (unfold map_fst_pair_spmf)
  by simp

definition is_uniform_sharing :: "natL sharing spmf \<Rightarrow> bool" where
  "is_uniform_sharing s \<longleftrightarrow> (\<exists>x :: natL spmf. s = bind_spmf x share_nat)"

definition is_uniform_sharing2 :: "(natL sharing \<times> natL sharing) spmf \<Rightarrow> bool" where
  "is_uniform_sharing2 s \<longleftrightarrow> (\<exists>xy :: (natL \<times> natL) spmf.
    s = bind_spmf xy (\<lambda>(x,y). pair_spmf (share_nat x) (share_nat y)))"


lemma share_nat_uniform:
  "is_uniform_sharing (share_nat x)"
  unfolding is_uniform_sharing_def
  apply (rule exI[where x="return_spmf x"])
  by simp

lemma share_nat_lossless:
  "lossless_spmf (share_nat x)"
  unfolding share_nat_def
  unfolding lossless_spmf_of_set
  apply rule
  subgoal
    by (rule finite_subset[where B=UNIV]) auto
  subgoal
    unfolding vimage_def
    apply simp
    apply (rule exI[where x="make_sharing x 0 0"])
    apply simp
    done
  done

lemma uniform_sharing2:
  "is_uniform_sharing s \<Longrightarrow> p1 \<noteq> p2 \<Longrightarrow> map_spmf (\<lambda>x. (get_party p1 x, get_party p2 x)) s = scale_spmf (weight_spmf s) (spmf_of_set UNIV)"
  unfolding is_uniform_sharing_def
  apply (erule exE)
  apply simp
  unfolding map_bind_spmf comp_def
  unfolding share_nat_2party_uniform
  unfolding bind_spmf_const
  unfolding weight_bind_spmf
  apply (subst Bochner_Integration.integral_cong[where g="\<lambda>_. 1"])
    apply (rule refl)
  subgoal using share_nat_lossless unfolding lossless_spmf_def by simp
  subgoal by simp
  done

lemma uniform_sharing:
  "is_uniform_sharing s \<Longrightarrow> map_spmf (get_party p) s = scale_spmf (weight_spmf s) (spmf_of_set UNIV)"
  supply [simp] = spmf.map_comp comp_def
  apply (unfold uniform_sharing2[where ?p1.0=p and ?p2.0="next_role p", THEN arg_cong[where f="map_spmf fst"], simplified])
  apply (fold UNIV_Times_UNIV)
  apply (fold pair_spmf_of_set)
  apply (unfold map_scale_spmf)
  by simp

lemma uniform_sharing':
  "\<lbrakk>is_uniform_sharing s; lossless_spmf s\<rbrakk> \<Longrightarrow> map_spmf (get_party p) s = spmf_of_set UNIV"
  by (simp add: uniform_sharing lossless_weight_spmfD)


lemma zero_masking_uniform:
  "p\<noteq>q \<Longrightarrow> (map_spmf ((\<lambda>t. (get_party p t, get_party q t)) \<circ> map_sharing2 (+) s) zero_sharing) = spmf_of_set UNIV"
proof -
  assume pq: "p\<noteq>q"
  obtain r where r: "q\<noteq>r" "r\<noteq>p" 
    using role_otherE .
  note [simp] = make_sharing'_sel[OF pq r]
  have inj: "inj (\<lambda>x. (get_party p s + fst x, get_party q s + snd x))"
    unfolding inj_def by simp
  have surj: "surj (\<lambda>x. (get_party p s + fst x, get_party q s + snd x))"
    by (rule finite_UNIV_inj_surj[OF _ inj]) simp
  show "(map_spmf ((\<lambda>t. (get_party p t, get_party q t)) \<circ> map_sharing2 (+) s) zero_sharing) = spmf_of_set UNIV"
    unfolding zero_sharing_def
    unfolding share_nat_def_calc'[OF pq r] Let_def case_prod_unfold
    unfolding map_spmf_conv_bind_spmf[symmetric] spmf.map_comp comp_def
    using inj surj by (auto simp: pair_spmf_of_set)
qed

lemma sharing_eqI2[consumes 3]:
  assumes "p1\<noteq>p2" "p2\<noteq>p3" "p3\<noteq>p1" "\<And>p. p\<in>{p1,p2,p3} \<Longrightarrow> get_party p s  = get_party p t"
  shows "s = t"
  by (smt (verit) assms Role.exhaust insert_commute insert_subset sharing_eqI' subset_insertI)

lemma sharing_map[simp]:
  assumes "p1\<noteq>p2" "p2\<noteq>p3" "p3\<noteq>p1"
  shows "map_sharing f (make_sharing' p1 p2 p3 x1 x2 x3) = make_sharing' p1 p2 p3 (f x1) (f x2) (f x3)"
  supply [simp] = make_sharing'_sel[OF assms]
  apply (rule sharing_eqI2[OF assms])
  by auto

lemma sharing_prod[simp]:
  assumes "p1\<noteq>p2" "p2\<noteq>p3" "p3\<noteq>p1"
  shows "prod_sharing (make_sharing' p1 p2 p3 x1 x2 x3) (make_sharing' p1 p2 p3 y1 y2 y3)
   = make_sharing' p1 p2 p3 (x1,y1) (x2,y2) (x3,y3)"
  supply [simp] = make_sharing'_sel[OF assms]
  apply (rule sharing_eqI2[OF assms])
  by auto

lemma add_sharing_inj:
  "inj (map_sharing2 (+) (s :: natL sharing))"
  apply (rule injI)
  subgoal for x y
    by (cases s; cases x; cases y) simp
  done

lemma add_sharing_surj:
  "surj (map_sharing2 (+) (s :: natL sharing))"
  apply (rule finite_UNIV_inj_surj)
  subgoal by simp
  subgoal using add_sharing_inj .
  done

lemma sharing_add_inv_eq_minus:
  "Hilbert_Choice.inv (map_sharing2 (+) (s::natL sharing)) t = map_sharing2 (-) t s"
  apply (rule inv_f_eq)
  subgoal using add_sharing_inj .
  by (cases s; cases t) simp

lemma zero_masking_eq_share_nat:
  "map_spmf (map_sharing2 (+) (s :: natL sharing)) zero_sharing = share_nat (reconstruct s)"
  unfolding zero_sharing_def share_nat_def
  apply (subst map_spmf_of_set_inj_on)
  subgoal
    apply (rule inj_on_subset[OF _ subset_UNIV])
    apply (rule add_sharing_inj)
    done
  apply (rule arg_cong[where f=spmf_of_set])
  apply (rule antisym)
  subgoal
    apply clarsimp
    subgoal for t
      apply (cases s; cases t)
      apply (auto simp: algebra_simps)
      done
    done
  subgoal
    apply clarsimp
    subgoal for t
      apply (cases s; cases t)
      apply clarsimp
      apply (rule image_eqI)
       apply (rule surj_f_inv_f[OF add_sharing_surj, symmetric])
      unfolding sharing_add_inv_eq_minus
      apply (auto simp: algebra_simps)
      done
    done
  done

lemma inv_uniform':
  assumes ss: "s \<subseteq> U" and inj: "inj_on f U"
  shows "map_spmf (\<lambda>x. (x, f x)) (spmf_of_set s) = map_spmf (\<lambda>y. (Hilbert_Choice.inv_into U f y, y)) (spmf_of_set (f ` s))"
  apply (subst map_spmf_of_set_inj_on)
  subgoal using inj_on_convol_ident .
  apply (subst map_spmf_of_set_inj_on)
  subgoal using assms by (simp add: inj_on_def)
  apply (rule arg_cong[where f=spmf_of_set])
  using assms by (auto simp: inv_into_f_f[OF inj] intro!: image_eqI)

lemma inv_uniform:
  "inj f \<Longrightarrow> map_spmf (\<lambda>x. (x, f x)) (spmf_of_set s) = map_spmf (\<lambda>y. (Hilbert_Choice.inv f y, y)) (spmf_of_set (f ` s))"
  using inv_uniform'[where U=UNIV, simplified] .

lemma reconstruct_plus:
  "reconstruct (map_sharing2 (+) x y) = reconstruct x + reconstruct y"
  by (cases x; cases y) simp

lemma reconstruct_minus:
  "reconstruct (map_sharing2 (-) x y) = reconstruct x - reconstruct y"
  by (cases x; cases y) simp

lemma plus_reconstruct:
  "map_sharing2 (+) x ` reconstruct -` {y} = reconstruct -` {reconstruct x + y}"
  supply [simp] = reconstruct_plus reconstruct_minus
  apply rule
  subgoal by auto
  subgoal
    unfolding vimage_def image_def
    apply clarsimp
    subgoal for t
      by (rule exI[where x="map_sharing2 (-) t x"]) auto
    done
  done

lemma inv_zero_sharing:
  "map_spmf (\<lambda>\<zeta>. (\<zeta>, map_sharing2 (+) x \<zeta>)) zero_sharing = map_spmf (\<lambda>y. (map_sharing2 (-) y x, y)) (share_nat (reconstruct x))"
  unfolding zero_sharing_def share_nat_def
  apply (subst inv_uniform)
  subgoal 
    using add_sharing_inj[THEN inj_on_subset] by auto
  apply (subst sharing_add_inv_eq_minus)
  apply (subst plus_reconstruct)
  apply simp
  done

lemma hoist_map_spmf:
  "(do {x \<leftarrow> s; g x (f x)}) = (do {(x,y) \<leftarrow> map_spmf (\<lambda>x. (x, f x)) s; g x y})"
  unfolding bind_map_spmf comp_def by simp

lemma hoist_map_spmf':
  "(do {x \<leftarrow> s; g x (f x)}) = (do {(y,x) \<leftarrow> map_spmf (\<lambda>x. (f x, x)) s; g x y})"
  unfolding bind_map_spmf comp_def by simp

definition "HOIST_TAG x = x"
lemmas hoist_tag = HOIST_TAG_def[symmetric]

lemma tagged_hoist_map_spmf:
  "(do {x \<leftarrow> s; g x (HOIST_TAG (f x))}) = (do {(x,y) \<leftarrow> map_spmf (\<lambda>x. (x, f x)) s; g x y})"
  unfolding HOIST_TAG_def using hoist_map_spmf .

lemma get_prev_sharing[simp]:
  "get_party p (shift_sharing s) = get_party (prev_role p) s"
  unfolding shift_sharing_def 
  by (cases p; simp)

lemma shift_sharing_make_sharing:
  "shift_sharing (make_sharing x1 x2 x3) = make_sharing x3 x1 x2"
  unfolding shift_sharing_def
  by simp

lemma reconstruct_share_nat:
    "map_spmf (\<lambda>xs. (xs, reconstruct xs)) (share_nat x) = map_spmf (\<lambda>xs. (xs, x)) (share_nat x)" for x
    unfolding share_nat_def by (auto cong: map_spmf_cong_simp)

lemma weight_share_nat:
  "weight_spmf (share_nat x) = 1"
  unfolding share_nat_def weight_spmf_of_set vimage_def
  apply clarsimp
  apply (rule exI[where x="make_sharing x 0 0"])
  apply simp
  done

end