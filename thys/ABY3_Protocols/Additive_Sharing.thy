theory Additive_Sharing
  imports
    CryptHOL.CryptHOL
    Finite_Number_Type
begin

datatype Role = Party1 | Party2 | Party3

lemma Role_exhaust'[dest!]:
  "r \<noteq> Party1 \<Longrightarrow> r \<noteq> Party2 \<Longrightarrow> r \<noteq> Party3 \<Longrightarrow> False"
  using Role.exhaust by blast

lemma Role_exhaust:
  "(r1::Role)\<noteq>r2 \<Longrightarrow> r2\<noteq>r3 \<Longrightarrow> r3\<noteq>r1 \<Longrightarrow> r=r1 \<or> r=r2 \<or> r=r3"
  by (metis Role.exhaust)

type_synonym 'a sharing = "Role \<Rightarrow> 'a"

instance Role :: finite
  apply (standard)
  by (metis (full_types) Role.exhaust ex_new_if_finite finite.intros(1) finite_insert insert_iff)

definition map_sharing :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a sharing \<Rightarrow> 'b sharing" where
  "map_sharing f x = f \<circ> x"

definition get_party :: "Role \<Rightarrow> 'a sharing \<Rightarrow> 'a" where
  "get_party r x = x r"

lemma map_sharing_sel[simp]:
  "get_party r (map_sharing f x) = f (get_party r x)"
  unfolding get_party_def map_sharing_def comp_def ..

definition make_sharing' :: "Role \<Rightarrow> Role \<Rightarrow> Role \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a sharing" where
  "make_sharing' r1 r2 r3 x1 x2 x3 = undefined(r1:=x1, r2:=x2, r3:=x3)"

abbreviation "make_sharing \<equiv> make_sharing' Party1 Party2 Party3"

lemma make_sharing'_sel:
  assumes "r1 \<noteq> r2" "r2 \<noteq> r3" "r3 \<noteq> r1"
  shows
    "get_party r1 (make_sharing' r1 r2 r3 x1 x2 x3) = x1"
    "get_party r2 (make_sharing' r1 r2 r3 x1 x2 x3) = x2"
    "get_party r3 (make_sharing' r1 r2 r3 x1 x2 x3) = x3"
  unfolding make_sharing'_def get_party_def
  using assms by simp_all

lemma make_sharing_sel[simp]:
  shows
    "get_party Party1 (make_sharing x1 x2 x3) = x1"
    "get_party Party2 (make_sharing x1 x2 x3) = x2"
    "get_party Party3 (make_sharing x1 x2 x3) = x3"
  by (simp_all add: make_sharing'_sel)

primrec next_role where
  "next_role Party1 = Party2"
| "next_role Party2 = Party3"
| "next_role Party3 = Party1"

primrec prev_role where
  "prev_role Party1 = Party3"
| "prev_role Party2 = Party1"
| "prev_role Party3 = Party2"

lemma next_sharing_neq_self[simp]:
  "next_role r = r \<longleftrightarrow> False" "r = next_role r \<longleftrightarrow> False"
  by (cases r; simp)+

lemma prev_sharing_neq_self[simp]:
  "prev_role r = r \<longleftrightarrow> False" "r = prev_role r \<longleftrightarrow> False"
  by (cases r; simp)+

lemma next_sharing_neq_prev[simp]:
  "next_role r = prev_role r \<longleftrightarrow> False" "prev_role r = next_role r \<longleftrightarrow> False"
  by (cases r; simp)+

lemma role_otherE:
  obtains r :: Role where "r0\<noteq>r" "r\<noteq>r1" 
  by (cases r0; cases r1) auto

lemma make_sharing_sel_p2:
  shows
    "get_party (prev_role r) (make_sharing' (prev_role r) r (next_role r) x1 x2 x3) = x1"
    "get_party r             (make_sharing' (prev_role r) r (next_role r) x1 x2 x3) = x2"
    "get_party (next_role r) (make_sharing' (prev_role r) r (next_role r) x1 x2 x3) = x3"
 using make_sharing'_sel[of "prev_role r" r "next_role r" x1 x2 x3, simplified] .

lemma sharing_cases[cases type]:
  obtains x1 x2 x3 where "s = make_sharing x1 x2 x3"
  subgoal premises P
    apply (rule P[of "s Party1" "s Party2" "s Party3"])
    apply (rule ext)
    subgoal for p
      unfolding make_sharing'_def by (cases p; simp)
    done
  done

lemma sharing_cases':
  assumes "p1\<noteq>p2" "p2\<noteq>p3" "p3\<noteq>p1"
  obtains x1 x2 x3 where "s = make_sharing' p1 p2 p3 x1 x2 x3"
  subgoal premises P
    apply (rule P[of "s p1" "s p2" "s p3"])
    apply (rule ext)
    subgoal for p
      unfolding make_sharing'_def using assms Role_exhaust by (cases p; auto)
    done
  done

lemma make_sharing_collapse[simp]:
  "make_sharing (get_party Party1 s) (get_party Party2 s) (get_party Party3 s) = s"
  by (cases s) simp

lemma sharing_eqI':
  "\<lbrakk>get_party Party1 x = get_party Party1 y;
    get_party Party2 x = get_party Party2 y;
    get_party Party3 x = get_party Party3 y\<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule ext)
  subgoal for r
    unfolding get_party_def by (cases r; simp)
  done

lemma sharing_eqI[intro]:
  "(\<And>r. get_party r x = get_party r y) \<Longrightarrow> x = y"
  apply (rule ext)
  subgoal for r
    unfolding get_party_def by (cases r; simp)
  done

abbreviation prod_sharing :: "'a sharing \<Rightarrow> 'b sharing \<Rightarrow> ('a \<times> 'b) sharing" where
  "prod_sharing \<equiv> corec_prod"

abbreviation map_sharing2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a sharing \<Rightarrow> 'b sharing \<Rightarrow> 'c sharing" where
  "map_sharing2 f xs ys \<equiv> map_sharing (case_prod f) (prod_sharing xs ys)"

lemma prod_sharing_sel[simp]:
  "get_party r (prod_sharing x y) = (get_party r x, get_party r y)"
  unfolding get_party_def corec_prod_apply ..

lemma prod_sharing_def_alt:
  "prod_sharing x y = make_sharing
    (get_party Party1 x, get_party Party1 y)
    (get_party Party2 x, get_party Party2 y)
    (get_party Party3 x, get_party Party3 y)"
  by (auto intro: sharing_eqI')

lemma prod_sharing_map_sel[simp]:
  "map_sharing fst (prod_sharing x y) = x"
  "map_sharing snd (prod_sharing x y) = y"
  unfolding map_sharing_def comp_def by simp_all


definition shift_sharing :: "'a sharing \<Rightarrow> 'a sharing" where
  "shift_sharing x = make_sharing (get_party Party3 x) (get_party Party1 x) (get_party Party2 x)"

lemma shift_sharing_def_alt:
  "shift_sharing x = x \<circ> (make_sharing Party3 Party1 Party2)"
  unfolding shift_sharing_def make_sharing'_def comp_def get_party_def
  by (auto)

type_synonym 'a repsharing = "('a \<times> 'a) sharing"

definition reshare :: "'a sharing \<Rightarrow> 'a repsharing" where
  "reshare s = prod_sharing (shift_sharing s) s"

lemma reshare_sel:
  "get_party Party1 (reshare s) = (get_party Party3 s, get_party Party1 s)"
  "get_party Party2 (reshare s) = (get_party Party1 s, get_party Party2 s)"
  "get_party Party3 (reshare s) = (get_party Party2 s, get_party Party3 s)"
  unfolding reshare_def shift_sharing_def
  by simp_all

definition derep_sharing :: "'a repsharing \<Rightarrow> 'a sharing" where
  "derep_sharing = map_sharing snd"

lemma derep_sharing_sel:
  "get_party r (derep_sharing s) = snd (get_party r s)"
  unfolding derep_sharing_def by simp

lemma derep_sharing_reshare[simp]:
  "derep_sharing (reshare s) = s"
  unfolding derep_sharing_def reshare_def by simp

definition map_repsharing :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a repsharing \<Rightarrow> 'b repsharing" where
  "map_repsharing f s = reshare (map_sharing f (derep_sharing s))"

lemma map_repsharing_reshare:
  "map_repsharing f (reshare s) = reshare (map_sharing f s)"
  unfolding map_repsharing_def by simp

definition valid_repsharing :: "'a repsharing \<Rightarrow> bool" where
  "valid_repsharing s \<longleftrightarrow> reshare (derep_sharing s) = s"

lemma valid_repsharingE:
  assumes "valid_repsharing s"
  obtains p where "s = reshare p"
  using assms unfolding valid_repsharing_def by metis

lemma map_repsharing_def_alt:
  "valid_repsharing s \<Longrightarrow> map_repsharing f s = map_sharing (map_prod f f) s"
  by (erule valid_repsharingE) (auto intro: sharing_eqI' simp: map_repsharing_reshare reshare_sel)

lemma reshare_derep_sharing[simp]:
  "valid_repsharing s \<Longrightarrow> reshare (derep_sharing s) = s"
  by (erule valid_repsharingE) simp

lemma valid_reshare[simp]:
  "valid_repsharing (reshare s)"
  unfolding valid_repsharing_def by simp

definition make_repsharing :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a repsharing" where
  "make_repsharing x1 x2 x3 = reshare (make_sharing x1 x2 x3)"

definition reconstruct :: "natL sharing \<Rightarrow> natL" where
  "reconstruct s = get_party Party1 s + get_party Party2 s + get_party Party3 s"

definition reconstruct_rep :: "natL repsharing \<Rightarrow> natL" where
  "reconstruct_rep s = reconstruct (derep_sharing s)"

lemma reconstruct_share[simp]:
  "reconstruct_rep (reshare s) = reconstruct s"
  unfolding reconstruct_rep_def by simp

lemma recontrust_def':
  assumes "r1\<noteq>r2" "r2\<noteq>r3" "r3\<noteq>r1"
  shows "reconstruct s = get_party r1 s + get_party r2 s + get_party r3 s"
  unfolding reconstruct_def
  using assms
  by (cases r1; cases r2; cases r3; simp)

lemma reconstruct_make_sharing'[simp]:
  assumes "r1 \<noteq> r2" "r2 \<noteq> r3" "r3 \<noteq> r1"
  shows "reconstruct (make_sharing' r1 r2 r3 x1 x2 x3) = x1 + x2 + x3"
  unfolding reconstruct_def
  unfolding make_sharing'_def get_party_def
  using assms
  by (cases r1; cases r2; cases r3; simp)

lemma reconstruct_make_repsharing[simp]:
  "reconstruct_rep (make_repsharing x1 x2 x3) = x1 + x2 + x3"
  unfolding make_repsharing_def
  unfolding reconstruct_share
  by simp

definition valid_nat_repsharing :: "natL \<Rightarrow> natL repsharing \<Rightarrow> bool" where
  "valid_nat_repsharing v s \<longleftrightarrow> reconstruct_rep s = v \<and> reshare (derep_sharing s) = s"

lemma comp_inj_on_iff':
  "inj_on (f' \<circ> f) A \<longleftrightarrow> inj_on f A \<and> inj_on f' (f ` A)"
  using comp_inj_on_iff inj_on_imageI inj_on_imageI2 by auto
  

lemma corec_prod_inject[simp]:
  "corec_prod f g = corec_prod f' g' \<longleftrightarrow> f = f' \<and> g = g'"
  unfolding corec_prod_def
  by (meson ext prod.inject)

lemma inj_on_corec_prodI:
  "inj_on f A \<or> inj_on g A \<Longrightarrow> inj_on (\<lambda>x. corec_prod (f x) (g x)) A"
  by (auto intro: inj_onI simp: inj_on_eq_iff)

lemma inj_on_reshare[simp]:
  "inj_on reshare A"
  unfolding reshare_def
  by (rule inj_on_corec_prodI) simp

lemma inj_on_make_repsharing_eq_sharing:
  "inj_on (\<lambda>x. make_repsharing (f x) (g x) (h x)) A \<longleftrightarrow> inj_on (\<lambda>x. make_sharing (f x) (g x) (h x)) A"
  unfolding make_repsharing_def
  unfolding comp_inj_on_iff'
  apply (subst comp_inj_on_iff'[unfolded comp_def, where f'=reshare])
  by auto

lemma make_sharing'_inject[simp]:
  assumes "r1\<noteq>r2" "r2\<noteq>r3" "r3\<noteq>r1"
  shows "make_sharing' r1 r2 r3 x1 x2 x3 = make_sharing' r1 r2 r3 y1 y2 y3 \<longleftrightarrow> x1=y1 \<and> x2=y2 \<and> x3=y3"
  using assms by (metis make_sharing'_sel)

lemma make_sharing_inject[simp]:
  "make_sharing x1 x2 x3 = make_sharing y1 y2 y3 \<longleftrightarrow> x1=y1 \<and> x2=y2 \<and> x3=y3"
  by simp

lemma reshare_inject[simp]:
  "reshare a = reshare b \<longleftrightarrow> a = b"
  unfolding reshare_def
  by auto

lemma make_repsharing_inject[simp]:
  "make_repsharing x1 x2 x3 = make_repsharing y1 y2 y3 \<longleftrightarrow> x1=y1 \<and> x2=y2 \<and> x3=y3"
  unfolding make_repsharing_def
  by simp

lemma inj_on_make_sharingI:
  "inj_on f A \<or> inj_on g A \<or> inj_on h A \<Longrightarrow> inj_on (\<lambda>x. make_sharing (f x) (g x) (h x)) A"
  by (auto intro: inj_onI simp: inj_on_eq_iff)

lemma inj_on_make_repsharingI:
  "inj_on f A \<or> inj_on g A \<or> inj_on h A \<Longrightarrow> inj_on (\<lambda>x. make_repsharing (f x) (g x) (h x)) A"
  unfolding inj_on_make_repsharing_eq_sharing using inj_on_make_sharingI .


(* monad transformer: set \<rightarrow> spmf *)

(* lift = spmf_of_set *)
(* return = return_spmf *)

lemma finite'_card_0: "finite' A \<longleftrightarrow> card A \<noteq> 0"
  and card_0_finite': "card A = 0 \<longleftrightarrow> \<not>finite' A"
  unfolding card_eq_0_iff by auto

lemma spmf_of_set_bind:
  assumes fin: "finite A"
    and disj: "disjoint_family_on f A"
    and card: "\<And>a. a\<in>A \<Longrightarrow> card (f a) = c"
  shows "spmf_of_set (A \<bind> f) = spmf_of_set A \<bind> (\<lambda>x. spmf_of_set (f x))"
    (* lift (A \<bind> f) = (lift A) \<bind> (lift \<circ> f) *)

proof -
  have card_bind: "card (A \<bind> f) = card A * c"
  proof -
    { assume c0: "c = 0"
      note card_UN_le[OF fin, folded bind_UNION, of f]
      hence ?thesis
        using card c0 by simp
    }
    moreover
    { assume cn0: "c \<noteq> 0"
      then have "finite (f a)" if "a\<in>A" for a
        using card[OF that] card_0_finite' by metis
      hence ?thesis
        unfolding bind_UNION
        using assms by (auto simp: card_UN_disjoint'[OF disj _ fin])
    }
    ultimately show ?thesis by blast
  qed
  show ?thesis
    apply (rule spmf_eqI)
    apply (unfold spmf_bind)
    apply (unfold integral_spmf_of_set)
    apply (unfold spmf_of_set)
    apply (unfold card_bind)
    apply (unfold indicator_UN_disjoint[folded bind_UNION, OF fin disj])
    apply (auto simp: card sum_divide_distrib[symmetric])
    done
qed

lemma ap_set_singleton:
  "ap_set {f} A = f ` A"
  by blast

lemma ap_set_Union:
  "ap_set F A = (\<Union>f\<in>F. f ` A)"
  unfolding ap_set_def by auto

lemma ap_set_curry:
  "ap_set (ap_set F A) B = ap_set (case_prod ` F) (A \<times> B)"
  unfolding ap_set_Union by auto

definition share_nat :: "natL \<Rightarrow> natL sharing spmf" where
  "share_nat x = spmf_of_set (reconstruct -` {x})"

definition zero_sharing :: "natL sharing spmf" where
  "zero_sharing = share_nat 0"

lemma share_nat_def_calc':
  assumes [simp]: "r1\<noteq>r2" "r2\<noteq>r3" "r3\<noteq>r1"
  shows
    "share_nat x = (do {
      (x1,x2) \<leftarrow> pair_spmf (spmf_of_set UNIV) (spmf_of_set UNIV);
      let x3 = x - (x1 + x2);
      return_spmf (make_sharing' r1 r2 r3 x1 x2 x3)
    })"
  apply (unfold pair_spmf_of_set)
  apply (unfold share_nat_def)
  apply (unfold Let_def)
  apply (unfold case_prod_unfold)
  apply (fold map_spmf_conv_bind_spmf)
  apply (subst map_spmf_of_set_inj_on)
  subgoal using assms by (auto intro: inj_onI)
  apply (rule arg_cong[where f=spmf_of_set])
  apply (rule Set.equalityI)
  subgoal
    apply (rule Set.subsetI)
    subgoal for xa
      by (cases xa rule: sharing_cases'[OF assms]) (auto simp: Set.image_iff)
    done
  subgoal using assms by auto
  done

lemma share_nat_def_calc:
  "share_nat x = (do {
    (x1,x2) \<leftarrow> spmf_of_set UNIV;
    let x3 = x - (x1 + x2);
    return_spmf (make_sharing x1 x2 x3)
  })"
  using share_nat_def_calc'[of Party1 Party2 Party3] by (simp add: pair_spmf_of_set)

definition repshare_nat :: "natL \<Rightarrow> natL repsharing spmf" where
  "repshare_nat x = (do {
    (x1,x2) \<leftarrow> spmf_of_set UNIV;
    let x3 = x - (x1 + x2);
    return_spmf (make_repsharing x1 x2 x3)
  })"

lemma repshare_nat_def_share:
  "repshare_nat x = map_spmf reshare (share_nat x)"
  unfolding share_nat_def_calc repshare_nat_def
  unfolding map_bind_spmf comp_def map_return_pmf make_repsharing_def case_prod_unfold
  by simp

lemma repshare_nat_def_alt:
  "repshare_nat x = spmf_of_set {reshare s | s. reconstruct s = x}"
  apply (unfold repshare_nat_def_share)
  apply (unfold share_nat_def)
  by (auto intro: arg_cong[where f=spmf_of_set])

lemma valid_nat_repsharing_reshare[simp]:
  "valid_nat_repsharing (reconstruct s) (reshare s)"
  unfolding valid_nat_repsharing_def
  unfolding reconstruct_share
  unfolding derep_sharing_reshare
  by simp

lemma valid_nat_repsharingE:
  assumes "valid_nat_repsharing x s"
  obtains s' where "s = reshare s'" and "reconstruct s' = x"
  subgoal premises prems
    apply (rule prems[of "derep_sharing s"])
    using assms unfolding valid_nat_repsharing_def reconstruct_rep_def by auto
  done

lemma repshare_nat_def_alt':
  "repshare_nat x = spmf_of_set (Collect (valid_nat_repsharing x))"
  unfolding repshare_nat_def_alt
  apply (rule arg_cong[where f=spmf_of_set])
  by (auto elim: valid_nat_repsharingE)

lemma share_nat_valid:
  "pred_spmf (valid_nat_repsharing x) (repshare_nat x)"
  unfolding repshare_nat_def_alt' by simp

lemma prod_sharing_map_fst_snd[simp]:
  "prod_sharing (map_sharing fst s) (map_sharing snd s) = s"
  by auto

end