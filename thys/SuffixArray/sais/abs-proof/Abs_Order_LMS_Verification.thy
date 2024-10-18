theory Abs_Order_LMS_Verification
  imports "../abs-def/Abs_SAIS"
begin

section "Order LMS-types Proofs"
(*
lemma abs_order_lms_app:
  "order_lms LMS (xs @ ys) = order_lms LMS xs @ order_lms LMS ys"
  by (induct xs arbitrary: ys; simp)

lemma rev_abs_order_lms:
  "rev (order_lms LMS xs) = order_lms LMS (rev xs)"
  by (induct xs rule: rev_induct; simp add: abs_order_lms_app)
*)

lemma abs_order_lms_eq_map_nth:
  "order_lms LMS xs = map (nth LMS) xs"
  by (induct xs; simp)

(*
lemma abs_order_lms_length:
  "length (order_lms LMS xs) = length xs"
  by (induct xs; simp)
*)

theorem distinct_abs_order_lms:
  "\<lbrakk>xs <~~> [0..<length LMS]; distinct LMS\<rbrakk> \<Longrightarrow>
    distinct (order_lms LMS xs)"
  apply (subst abs_order_lms_eq_map_nth)
  apply (erule distinct_map_nth_perm[of _ "length LMS"]; simp)
  done

theorem abs_order_lms_eq_all_lms:
  "\<lbrakk>xs <~~> [0..<length LMS]; set LMS = S\<rbrakk> \<Longrightarrow>
    set (order_lms LMS xs) = S"
  apply (subst abs_order_lms_eq_map_nth)
  apply (frule set_map_nth_perm_eq)
  apply simp
  done

end