theory Multiplication
  imports
    Additive_Sharing
    Spmf_Common
    Sharing_Lemmas
begin

text \<open>
This is the formalisation of ABY3's multiplication protocol.
We manually book-keep the messages to be simulated,
and we manually define the simulator used in the simulation proof.
\<close>

definition do_mul :: "(natL \<times> natL) \<Rightarrow> (natL \<times> natL) \<Rightarrow> natL" where
  "do_mul xy1 xy2 = fst xy1 * snd xy1 + fst xy1 * snd xy2 + fst xy2 * snd xy1"

type_synonym mul_in = "natL \<times> natL"  (* x, y *)
type_synonym mul_msg = "(natL \<times> natL) \<times> natL"  (* zero-sharing, other-x, other-y *)
type_synonym mul_view = "mul_in \<times> mul_msg"
type_synonym mul_out = "natL"  (* z *)

definition aby3_mulR :: "mul_in sharing \<Rightarrow> (mul_msg sharing \<times> mul_out sharing) spmf" where
  "aby3_mulR xy = (do {
    let xy_shift = shift_sharing xy;
    let z_raw = map_sharing2 do_mul xy xy_shift;
    \<zeta> \<leftarrow> zero_sharing;
    let z = map_sharing2 (+) z_raw \<zeta>;
    let msg = prod_sharing xy_shift \<zeta>;
    return_spmf (msg, z)
  })"

definition aby3_mulF :: "mul_in sharing \<Rightarrow> mul_out sharing spmf" where
  "aby3_mulF xy = (
    let x = reconstruct (map_sharing fst xy);
        y = reconstruct (map_sharing snd xy)
    in share_nat (x * y))"


definition S :: "mul_in \<Rightarrow> mul_out \<Rightarrow> mul_msg spmf" where
  "S inp outp = (do {
    let (x1, y1) = inp;
    (x2, y2) \<leftarrow> spmf_of_set UNIV;
    let \<zeta> = outp - do_mul (x1, y1) (x2, y2);
    return_spmf ((x2, y2), \<zeta>)
  })"


lemma reconstruct_do_mul:
  "reconstruct (map_sharing2 do_mul xys (shift_sharing xys)) = reconstruct (map_sharing fst xys) * reconstruct (map_sharing snd xys)"
  supply [simp] = shift_sharing_make_sharing do_mul_def
  by (cases xys) (auto simp: algebra_simps)

(* Semi-honest security and correctness of the multiplication protocol. *)
(* ?uniform asserts that the result is uniformly distributed *)
(* More structured proof can be found in the refactored formalization: Multiplication_Synthesization *)
theorem mul_spec:
  fixes x_dist y_dist :: "natL sharing spmf"
  assumes "is_uniform_sharing x_dist" "is_uniform_sharing y_dist"
  shows
    secure:
    "(do {
       xs \<leftarrow> x_dist;
       ys \<leftarrow> y_dist;
       let inps = prod_sharing xs ys;
       (msgs, outps) \<leftarrow> (aby3_mulR inps);
       let view = (get_party p inps, get_party p msgs);
       return_spmf (view, outps)
     })
     =
     (do {
       xs \<leftarrow> x_dist;
       ys \<leftarrow> y_dist;
       let inps = prod_sharing xs ys;
       outps \<leftarrow> aby3_mulF inps;
       msg \<leftarrow> S (get_party p inps) (get_party p outps);
       let view = (get_party p inps, msg);
       return_spmf (view, outps)
     })" (is ?secure)
    and
    correct:
    "is_uniform_sharing (do {
      xs \<leftarrow> x_dist;
      ys \<leftarrow> y_dist;
      aby3_mulF (prod_sharing xs ys)
    })" (is ?uniform)
proof -
  obtain xd yd where xd: "x_dist = bind_spmf xd share_nat" and yd: "y_dist = bind_spmf yd share_nat"
    using assms unfolding is_uniform_sharing_def by auto
  show ?secure
    unfolding aby3_mulR_def xd yd
    apply (subst (3) hoist_map_spmf[where f="map_sharing2 (+) _"])
    apply (subst inv_zero_sharing)
    apply (unfold bind_map_spmf comp_def prod.case)
    unfolding Let_def
    apply (subst reconstruct_do_mul)
    unfolding bind_spmf_assoc
    apply (unfold prod_sharing_map_sel)
    apply (subst hoist_map_spmf[where f="reconstruct"])
    apply (subst hoist_map_spmf[where f="reconstruct"])
    apply (unfold reconstruct_share_nat)
    apply (unfold bind_map_spmf comp_def prod.case)
    unfolding return_bind_spmf prod.case
    unfolding prod_sharing_sel get_prev_sharing map_sharing_sel prod.case
    apply (subst (1 2) share_nat_def_calc'[of "prev_role p" p "next_role p", unfolded case_prod_unfold, simplified])
    unfolding bind_spmf_assoc return_bind_spmf
    unfolding make_sharing_sel_p2
      (* done left *)
    apply (subst (2 3) share_nat_def_calc'[of "prev_role p" p "next_role p", simplified, abs_def])
    unfolding case_prod_unfold Let_def
    unfolding aby3_mulF_def S_def
    apply (clarsimp simp add: bind_commute_spmf[where q=yd] bind_commute_spmf[where q="share_nat _"])
    supply [simp del] = UNIV_Times_UNIV
    apply (fold UNIV_Times_UNIV )
    apply (fold pair_spmf_of_set)
    apply (unfold pair_spmf_alt_def)
    apply clarsimp
    unfolding make_sharing_sel_p2
    apply (subst bind_spmf_const, simp)
    apply (subst bind_spmf_const, simp)
    apply (rule arg_cong[where f="bind_spmf _"], rule)
    apply (rule arg_cong[where f="bind_spmf _"], rule)
    apply (rule arg_cong[where f="bind_spmf _"], rule)
    apply (subst (3) bind_commute_spmf)
    apply (subst (1) bind_commute_spmf)
    apply (subst (2) bind_commute_spmf)
    apply simp
      (* done right *)
    done

  show ?uniform
    unfolding xd yd aby3_mulF_def
    unfolding prod_sharing_map_sel
    unfolding bind_spmf_assoc
    apply (subst (1 2) hoist_map_spmf[where f="reconstruct"])
    apply (unfold reconstruct_share_nat)
    unfolding bind_map_spmf comp_def prod.case Let_def
    unfolding bind_commute_spmf[where q=yd]
    apply (fold pair_spmf_alt_def[of yd xd, THEN arg_cong[where f="\<lambda>x. bind_spmf x (case_prod _)"], simplified])
    unfolding bind_spmf_const weight_share_nat scale_spmf_1
    unfolding case_prod_unfold
    apply (fold bind_map_spmf[where f="\<lambda>x. snd x * fst x", unfolded comp_def])
    unfolding is_uniform_sharing_def
    by auto
qed

end