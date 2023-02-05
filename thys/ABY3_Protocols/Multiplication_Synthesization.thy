theory Multiplication_Synthesization
  imports
    Multiplication
begin

text \<open>
This is an experimental re-formalization of the multiplication protocol,
which differs from the original one in three aspects:
1) We use the writer transformer for automatic bookkeeping of simulation obligations in the privacy proof.
Since monad transformers are hard to deal with in HOL,
we combine (writer transformer + spmf monad) into writer\_spmf.
To ease the modelling, we allow heterogeneous message types in the binding operation,
a technicality that might disqualify it as a monad but, luckily, does not stop us from
using the built-in do-notation.
2) We wraps the adding of zero-sharing into a new operation called ``sharing flattening''.
The proof for the sharing flattening is then ``composed'' into the larger proof for multiplication.
3) The simulator is not manually defined but synthesized through @{command schematic_goal}.
\<close>

type_synonym ('val, 'msg) writer_spmf = "('val \<times> 'msg) spmf"

definition bind_writer_spmf :: "('val1, 'msg1) writer_spmf \<Rightarrow> ('val1 \<Rightarrow> ('val2, 'msg2) writer_spmf) \<Rightarrow> ('val2, ('msg1 \<times> 'msg2)) writer_spmf" where
  "bind_writer_spmf x f = bind_spmf x (\<lambda>(val1, msg1). map_spmf (\<lambda>(val2, msg2). (val2, (msg1, msg2))) (f val1))"

adhoc_overloading Monad_Syntax.bind bind_writer_spmf

definition flatten_sharingF :: "natL sharing \<Rightarrow> natL sharing spmf" where
  "flatten_sharingF s = share_nat (reconstruct s)"

definition flatten_sharingR :: "Role \<Rightarrow> natL sharing \<Rightarrow> (natL sharing, natL) writer_spmf" where
  "flatten_sharingR p s = do {
    \<zeta> \<leftarrow> zero_sharing;
    let r = map_sharing2 (+) s \<zeta>;
    return_spmf (r, (get_party p \<zeta>))
  }"

(* role-independent *)
definition flatten_sharingS :: "natL \<Rightarrow> natL \<Rightarrow> natL spmf" where
  "flatten_sharingS inp outp = return_spmf (outp - inp)"

lemma flatten_sharing_spec:
  "flatten_sharingR p x = do {
    y \<leftarrow> flatten_sharingF x;
    msg \<leftarrow> flatten_sharingS (get_party p x) (get_party p y);
    return_spmf (y, msg)
  }"
  unfolding flatten_sharingR_def
  unfolding flatten_sharingF_def
  unfolding flatten_sharingS_def
  apply simp
  apply (fold zero_masking_eq_share_nat)
  unfolding map_spmf_conv_bind_spmf
  apply simp
  done
(*
definition aby3_mulR' :: "mul_in sharing \<Rightarrow> (mul_msg sharing \<times> mul_out sharing) spmf" where
  "aby3_mulR' xy = (do {
    let xy_shift = shift_sharing xy;              \<comment> \<open>P_i \<leftarrow> (x_{i-1},y_{i-1})\<close>
    let z_raw = map_sharing2 do_mul xy xy_shift;  \<comment> \<open>z_raw_i := x_{i-1}*y_{i-1} + x_{i-1}*y_i + x_1*y_{i-1}\<close>
    \<zeta> \<leftarrow> zero_sharing;
    let z = map_sharing2 (+) z_raw \<zeta>;             \<comment> \<open>z_i := z_raw_i + \<zeta>_i\<close>
    let msg = prod_sharing xy_shift \<zeta>;            \<comment> \<open>msg_i := (x_{i-1},y_{i-1})\<close>
    return_spmf (msg, z)
  })"
*)

definition aby3_mulR' :: "Role \<Rightarrow> natL \<Rightarrow> natL \<Rightarrow> (natL sharing, ((natL \<times> natL) \<times> (natL \<times> natL)) \<times> natL) writer_spmf" where
  "aby3_mulR' p x y = do {
    xs \<leftarrow> share_nat x;
    ys \<leftarrow> share_nat y;
    let xy = prod_sharing xs ys;
    let xy_shift = shift_sharing xy;
    let z_raw = map_sharing2 do_mul xy xy_shift;
    (z, \<zeta>_msg) \<leftarrow> flatten_sharingR p z_raw;
    return_spmf (z, (((get_party p xs, get_party p ys), get_party p xy_shift), \<zeta>_msg))
  }"

definition aby3_mulF' :: "natL \<Rightarrow> natL \<Rightarrow> natL sharing spmf" where
  "aby3_mulF' x y = share_nat (x * y)"

(* role-irrelevant *)
definition aby3_mulS' :: "natL \<Rightarrow> (((natL \<times> natL) \<times> (natL \<times> natL)) \<times> natL) spmf" where
  "aby3_mulS' z = do {
    x1 \<leftarrow> spmf_of_set UNIV;
    x2 \<leftarrow> spmf_of_set UNIV;
    y1 \<leftarrow> spmf_of_set UNIV;
    y2 \<leftarrow> spmf_of_set UNIV;
    let \<zeta> = z - (x1 * y1 + x1 * y2 + x2 * y1);
    return_spmf (((x1, y1), (x2, y2)), \<zeta>)
  }"


lemma set_spmf_share_nat:
  "set_spmf (share_nat x) = {s. reconstruct s = x}"
  unfolding share_nat_def
  apply simp
  unfolding vimage_def
  apply simp
  done

lemma reconstruct_share_nat':
  "pred_spmf (\<lambda>s. reconstruct s = x) (share_nat x)"
  unfolding pred_spmf_def
  apply auto
  unfolding set_spmf_share_nat
  apply simp
  done

lemma share_nat_cong:
  "x = y \<Longrightarrow> (\<And>s. reconstruct s = x \<Longrightarrow> f s = g s) \<Longrightarrow> bind_spmf (share_nat x) f = bind_spmf (share_nat y) g"
  apply (rule bind_spmf_cong)
  subgoal by simp
  subgoal unfolding set_spmf_share_nat by simp
  done

lemma return_ResSim:
  "return_spmf (r, s) = bind_spmf (return_spmf s) (\<lambda>msg. return_spmf (r, msg))"
  by simp

schematic_goal aby3_mul_spec:
  "aby3_mulR' p x y =
    bind_spmf (aby3_mulF' x y) (\<lambda>z.
    bind_spmf (?aby3_mulS' (get_party p z)) (\<lambda>msg.
    return_spmf (z, msg)))"
  unfolding aby3_mulR'_def
  unfolding flatten_sharing_spec
  unfolding aby3_mulF'_def
  unfolding flatten_sharingF_def
  apply simp
  unfolding reconstruct_do_mul
  apply simp
  unfolding do_mul_def
  apply simp
  apply (simp cong: share_nat_cong)
  unfolding share_nat_def_calc'[of p "prev_role p" "next_role p" x, simplified]
  unfolding share_nat_def_calc'[of p "prev_role p" "next_role p" y, simplified]
  unfolding pair_spmf_alt_def
  apply simp
  unfolding make_sharing'_sel[of p "prev_role p" "next_role p", simplified]
  unfolding bind_commute_spmf[where q="share_nat _"]  
  apply (rule share_nat_cong[OF refl])
(* basically done here *)
  apply (subst return_ResSim)
  apply (fold bind_spmf_assoc)
  apply (rule refl)
  done

end