(*<*)
theory Restrict_Bounds_Impl
imports Restrict_Bounds
begin
(*>*)

section \<open>Refining the Non-Deterministic @{term simplification.rb} Function\<close>

fun gen_size where
  "gen_size (Bool b) = 1"
| "gen_size (Eq x t) = 1"
| "gen_size (Pred p ts) = 1"
| "gen_size (Neg (Neg Q)) = Suc (gen_size Q)"
| "gen_size (Neg (Conj Q1 Q2)) = Suc (Suc (gen_size (Neg Q1) + gen_size (Neg Q2)))"
| "gen_size (Neg (Disj Q1 Q2)) = Suc (Suc (gen_size (Neg Q1) + gen_size (Neg Q2)))"
| "gen_size (Neg Q) = Suc (gen_size Q)"
| "gen_size (Conj Q1 Q2) = Suc (gen_size Q1 + gen_size Q2)"
| "gen_size (Disj Q1 Q2) = Suc (gen_size Q1 + gen_size Q2)"
| "gen_size (Exists x Q) = Suc (gen_size Q)"


function (sequential) gen_impl where
  "gen_impl x (Bool False) = [{}]"
| "gen_impl x (Bool True) = []"
| "gen_impl x (Eq y (Const c)) = (if x = y then [{Eq y (Const c)}] else [])"
| "gen_impl x (Eq y (Var z)) = []"
| "gen_impl x (Pred p ts) = (if x \<in> fv_terms_set ts then [{Pred p ts}] else [])"
| "gen_impl x (Neg (Neg Q)) = gen_impl x Q"
| "gen_impl x (Neg (Conj Q1 Q2)) = gen_impl x (Disj (Neg Q1) (Neg Q2))"
| "gen_impl x (Neg (Disj Q1 Q2)) = gen_impl x (Conj (Neg Q1) (Neg Q2))"
| "gen_impl x (Neg _) = []"
| "gen_impl x (Disj Q1 Q2) =  [G1 \<union> G2. G1 \<leftarrow> gen_impl x Q1, G2 \<leftarrow> gen_impl x Q2]"
| "gen_impl x (Conj Q1 (y \<approx> z)) = (if x = y then List.union (gen_impl x Q1) (map (image (\<lambda>Q. cp (Q[z \<^bold>\<rightarrow> x]))) (gen_impl z Q1))
     else if x = z then List.union (gen_impl x Q1) (map (image (\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x]))) (gen_impl y Q1))
     else gen_impl x Q1)"|
 "gen_impl x (Conj Q1 Q2) = List.union (gen_impl x Q1) (gen_impl x Q2)"
| "gen_impl x (Exists y Q) = (if x = y then [] else map (image (exists y)) (gen_impl x Q))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(x, Q). gen_size Q)") simp_all

lemma gen_impl_gen: "G \<in> set (gen_impl x Q) \<Longrightarrow> gen x Q G"
  by (induct x Q arbitrary: G rule: gen_impl.induct)
    (auto 5 2 simp: fv_terms_set_def intro: gen.intros simp: image_iff split: if_splits)

lemma gen_gen_impl: "gen x Q G \<Longrightarrow> G \<in> set (gen_impl x Q)"
proof (induct x Q G rule: gen.induct)
  case (7 x Q1 G Q2)
  then show ?case
  proof (cases Q2)
    case (Eq x t)
    with 7 show ?thesis
      by (cases t) auto
  qed auto
qed (auto elim!: ap.cases simp: image_iff)

lemma set_gen_impl: "set (gen_impl x Q) = {G. gen x Q G}"
  by (auto simp: gen_impl_gen gen_gen_impl)

definition "flat xss = fold List.union xss []"

(*much faster than fun*)
primrec cov_impl where
  "cov_impl x (Bool b) = [{}]"
| "cov_impl x (Eq y t) = (case t of
      Const c \<Rightarrow> [if x = y then {Eq y (Const c)} else {}]
    | Var z \<Rightarrow> [if x = y \<and> x \<noteq> z then {x \<approx> z} 
                else if x = z \<and> x \<noteq> y then {x \<approx> y}
                else {}])"
| "cov_impl x (Pred p ts) = [if x \<in> fv_terms_set ts then {Pred p ts} else {}]"
| "cov_impl x (Neg Q) = cov_impl x Q"
| "cov_impl x (Disj Q1 Q2) = (case (cp (Q1 \<^bold>\<bottom> x), cp (Q2 \<^bold>\<bottom> x)) of
     (Bool True, Bool True) \<Rightarrow> List.union (cov_impl x Q1) (cov_impl x Q2)
   | (Bool True, _) \<Rightarrow> cov_impl x Q1
   | (_, Bool True) \<Rightarrow> cov_impl x Q2
   | (_, _) \<Rightarrow> [G1 \<union> G2. G1 \<leftarrow> cov_impl x Q1, G2 \<leftarrow> cov_impl x Q2])"
| "cov_impl x (Conj Q1 Q2) = (case (cp (Q1 \<^bold>\<bottom> x), cp (Q2 \<^bold>\<bottom> x)) of
     (Bool False, Bool False) \<Rightarrow> List.union (cov_impl x Q1) (cov_impl x Q2)
   | (Bool False, _) \<Rightarrow> cov_impl x Q1
   | (_, Bool False) \<Rightarrow> cov_impl x Q2
   | (_, _) \<Rightarrow> [G1 \<union> G2. G1 \<leftarrow> cov_impl x Q1, G2 \<leftarrow> cov_impl x Q2])"
| "cov_impl x (Exists y Q) = (if x = y then [{}] else flat (map (\<lambda>G.
     (if x \<approx> y \<in> G then [exists y ` (G - {x \<approx> y}) \<union> (\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` G'. G' \<leftarrow> gen_impl y Q]
      else [exists y ` G])) (cov_impl x Q)))"

lemma union_empty_iff: "List.union xs ys = [] \<longleftrightarrow> xs = [] \<and> ys = []"
  by (induct xs arbitrary: ys) (force simp: List.union_def List.insert_def)+

lemma fold_union_empty_iff: "fold List.union xss ys = [] \<longleftrightarrow> (\<forall>xs \<in> set xss. xs = []) \<and> ys = []"
  by (induct xss arbitrary: ys) (auto simp: union_empty_iff)

lemma flat_empty_iff: "flat xss = [] \<longleftrightarrow> (\<forall>xs \<in> set xss. xs = [])"
  by (auto simp: flat_def fold_union_empty_iff)

lemma set_fold_union: "set (fold List.union xss ys) = (\<Union> (set ` set xss)) \<union> set ys"
  by (induct xss arbitrary: ys) auto

lemma set_flat: "set (flat xss) = \<Union> (set ` set xss)"
  unfolding flat_def by (auto simp: set_fold_union)

lemma rrb_cov_impl: "rrb Q \<Longrightarrow> cov_impl x Q \<noteq> []"
proof (induct Q arbitrary: x)
  case (Exists y Q)
  then show ?case
    by (cases "\<exists>G \<in> set (cov_impl x Q). x \<approx> y \<in> G")
      (auto simp: flat_empty_iff image_iff dest: gen_gen_impl intro!: UnI1 bexI[rotated])
qed (auto split: term.splits fmla.splits bool.splits simp: union_empty_iff)

lemma cov_Eq_self: "cov x (y \<approx> y) {}"
  by (metis Un_absorb cov.Eq_self cov.nonfree fv.simps(3) fv_term_set.simps(1) singletonD)

lemma cov_impl_cov: "G \<in> set (cov_impl x Q) \<Longrightarrow> cov x Q G"
proof (induct Q arbitrary: x G)
  case (Eq y t)
  then show ?case
    by (auto simp: cov_Eq_self intro: cov.intros ap.intros split: term.splits)
qed (auto simp: set_flat set_gen_impl intro: cov.intros ap.intros
  split: term.splits fmla.splits bool.splits if_splits)

definition "fixbound_impl \<Q> x = filter (\<lambda>Q. x \<in> fv Q \<and> gen_impl x Q = []) (sorted_list_of_set \<Q>)"

lemma set_fixbound_impl: "finite \<Q> \<Longrightarrow> set (fixbound_impl \<Q> x) = fixbound \<Q> x"
  by (auto simp: fixbound_def nongens_def fixbound_impl_def set_gen_impl
    dest: arg_cong[of _ _ set] simp flip: List.set_empty)

lemma fixbound_empty_iff: "finite \<Q> \<Longrightarrow> fixbound \<Q> x \<noteq> {} \<longleftrightarrow> fixbound_impl \<Q> x \<noteq> []"
  by (auto simp: set_fixbound_impl dest: arg_cong[of _ _ set] simp flip: List.set_empty)

lemma fixbound_impl_hd_in: "finite \<Q> \<Longrightarrow> fixbound_impl \<Q> x = y # ys \<Longrightarrow> y \<in> \<Q>"
  by (auto simp: fixbound_impl_def dest!: arg_cong[of _ _ set])

fun (in simplification) rb_impl :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> ('a, 'b) fmla nres" where
  "rb_impl (Neg Q) = do { Q' \<leftarrow> rb_impl Q; RETURN (simp (Neg Q'))}"
| "rb_impl (Disj Q1 Q2) = do { Q1' \<leftarrow> rb_impl Q1; Q2' \<leftarrow> rb_impl Q2; RETURN (simp (Disj Q1' Q2'))}"
| "rb_impl (Conj Q1 Q2) = do { Q1' \<leftarrow> rb_impl Q1; Q2' \<leftarrow> rb_impl Q2; RETURN (simp (Conj Q1' Q2'))}"
| "rb_impl (Exists x Q) = do {
    Q' \<leftarrow> rb_impl Q;
    \<Q> \<leftarrow> WHILE
      (\<lambda>\<Q>. fixbound_impl \<Q> x \<noteq> []) (\<lambda>\<Q>. do {
        Qfix \<leftarrow> RETURN (hd (fixbound_impl \<Q> x));
        G \<leftarrow> RETURN (hd (cov_impl x Qfix));
        RETURN (\<Q> - {Qfix} \<union>
          {simp (Conj Qfix (DISJ (qps G)))} \<union>
          (\<Union>y \<in> eqs x G. {cp (Qfix[x \<^bold>\<rightarrow> y])}) \<union>
          {cp (Qfix \<^bold>\<bottom> x)})})
      (flat_Disj Q');
    RETURN (simp (DISJ (exists x ` \<Q>)))}"
| "rb_impl Q = do { RETURN (simp Q) }"

lemma (in simplification) rb_impl_refines_rb: "rb_impl Q \<le> rb Q"
  apply (induct Q)
  apply (unfold rb.simps rb_impl.simps)
  apply refine_mono
  apply refine_mono
  apply refine_mono
  apply refine_mono
  apply refine_mono
  apply refine_mono
  apply refine_mono
  subgoal for x Q' Q
    apply (rule order_trans[OF WHILE_le_WHILEI[where I="rb_INV x Q"]])
    apply (rule order_trans[OF WHILEI_le_WHILEIT])
    apply (rule WHILEIT_refine[OF _ _ _ refine_IdI, THEN refine_IdD])
       apply (simp_all add: fixbound_empty_iff) [3]
    apply refine_mono
      apply (auto simp flip: set_fixbound_impl simp: neq_Nil_conv fixbound_impl_hd_in
        intro!: cov_impl_cov rrb_cov_impl hd_in_set rb_INV_rrb)
    done
  done

fun (in simplification) rb_impl_det :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> ('a, 'b) fmla dres" where
  "rb_impl_det (Neg Q) = do { Q' \<leftarrow> rb_impl_det Q; dRETURN (simp (Neg Q'))}"
| "rb_impl_det (Disj Q1 Q2) = do { Q1' \<leftarrow> rb_impl_det Q1; Q2' \<leftarrow> rb_impl_det Q2; dRETURN (simp (Disj Q1' Q2'))}"
| "rb_impl_det (Conj Q1 Q2) = do { Q1' \<leftarrow> rb_impl_det Q1; Q2' \<leftarrow> rb_impl_det Q2; dRETURN (simp (Conj Q1' Q2'))}"
| "rb_impl_det (Exists x Q) = do {
    Q' \<leftarrow> rb_impl_det Q;
    \<Q> \<leftarrow> dWHILE
      (\<lambda>\<Q>. fixbound_impl \<Q> x \<noteq> []) (\<lambda>\<Q>. do {
        Qfix \<leftarrow> dRETURN (hd (fixbound_impl \<Q> x));
        G \<leftarrow> dRETURN (hd (cov_impl x Qfix));
        dRETURN (\<Q> - {Qfix} \<union>
          {simp (Conj Qfix (DISJ (qps G)))} \<union>
          (\<Union>y \<in> eqs x G. {cp (Qfix[x \<^bold>\<rightarrow> y])}) \<union>
          {cp (Qfix \<^bold>\<bottom> x)})})
      (flat_Disj Q');
    dRETURN (simp (DISJ (exists x ` \<Q>)))}"
| "rb_impl_det Q = do { dRETURN (simp Q) }"

lemma (in simplification) rb_impl_det_refines_rb_impl: "nres_of (rb_impl_det Q) \<le> rb_impl Q"
  by (induct Q; unfold rb_impl.simps rb_impl_det.simps) refine_transfer+

lemmas (in simplification) RB_correct =
  rb_impl_det_refines_rb_impl[THEN order_trans, OF
  rb_impl_refines_rb[THEN order_trans, OF
  rb_correct]]

(*<*)
end
(*>*)