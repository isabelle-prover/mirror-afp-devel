theory Carrier_Group_Scaffold
  imports Main
begin

section \<open>Groups on carriers\<close>

text \<open>
  The main Seifert--van Kampen statement is formulated on concrete carrier sets
  rather than on type-class groups. This locale package isolates the carrier
  algebra laws and homomorphism notions that the amalgamation and
  fundamental-group constructions need later on.
\<close>

locale carrier_group =
  fixes G :: "'a set"
    and mult :: "'a => 'a => 'a"
    and one :: "'a"
    and inv :: "'a => 'a"
  assumes one_closed [intro, simp]: "one \<in> G"
    and mult_closed [intro]: "\<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> mult x y \<in> G"
    and inv_closed [intro]: "x \<in> G \<Longrightarrow> inv x \<in> G"
    and mult_assoc: "\<lbrakk>x \<in> G; y \<in> G; z \<in> G\<rbrakk> \<Longrightarrow> mult (mult x y) z = mult x (mult y z)"
    and mult_one_left: "x \<in> G \<Longrightarrow> mult one x = x"
    and mult_one_right: "x \<in> G \<Longrightarrow> mult x one = x"
    and mult_inv_left: "x \<in> G \<Longrightarrow> mult (inv x) x = one"
    and mult_inv_right: "x \<in> G \<Longrightarrow> mult x (inv x) = one"
begin

lemma left_cancel:
  assumes x: "x \<in> G"
    and y: "y \<in> G"
    and z: "z \<in> G"
    and eq: "mult x y = mult x z"
  shows "y = z"
proof -
  have "mult (inv x) (mult x y) = mult (inv x) (mult x z)"
    using eq by simp
  moreover have "mult (inv x) (mult x y) = y"
  proof -
    have "mult (inv x) (mult x y) = mult (mult (inv x) x) y"
      using x y inv_closed[OF x] by (simp add: mult_assoc[symmetric])
    also have "... = y"
      using x y by (simp add: mult_inv_left mult_one_left)
    finally show ?thesis .
  qed
  moreover have "mult (inv x) (mult x z) = z"
  proof -
    have "mult (inv x) (mult x z) = mult (mult (inv x) x) z"
      using x z inv_closed[OF x] by (simp add: mult_assoc[symmetric])
    also have "... = z"
      using x z by (simp add: mult_inv_left mult_one_left)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by simp
qed

lemma right_cancel:
  assumes x: "x \<in> G"
    and y: "y \<in> G"
    and z: "z \<in> G"
    and eq: "mult y x = mult z x"
  shows "y = z"
proof -
  have "mult (mult y x) (inv x) = mult (mult z x) (inv x)"
    using eq by simp
  moreover have "mult (mult y x) (inv x) = y"
  proof -
    have "mult (mult y x) (inv x) = mult y (mult x (inv x))"
      using x y inv_closed[OF x] by (simp add: mult_assoc)
    also have "... = y"
      using x y by (simp add: mult_inv_right mult_one_right)
    finally show ?thesis .
  qed
  moreover have "mult (mult z x) (inv x) = z"
  proof -
    have "mult (mult z x) (inv x) = mult z (mult x (inv x))"
      using x z inv_closed[OF x] by (simp add: mult_assoc)
    also have "... = z"
      using x z by (simp add: mult_inv_right mult_one_right)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by simp
qed

lemma left_inverse_unique:
  assumes x: "x \<in> G"
    and y: "y \<in> G"
    and eq: "mult y x = one"
  shows "y = inv x"
proof (rule right_cancel[OF x y inv_closed[OF x]])
  show "mult y x = mult (inv x) x"
    using eq x by (simp add: mult_inv_left)
qed

lemma right_inverse_unique:
  assumes x: "x \<in> G"
    and y: "y \<in> G"
    and eq: "mult x y = one"
  shows "y = inv x"
proof (rule left_cancel[OF x y inv_closed[OF x]])
  show "mult x y = mult x (inv x)"
    using eq x by (simp add: mult_inv_right)
qed

end

locale carrier_group_hom =
  G: carrier_group G mult one inv +
  H: carrier_group H mult' one' inv'
  for G :: "'a set" and mult :: "'a => 'a => 'a" and one :: "'a" and inv :: "'a => 'a"
    and H :: "'b set" and mult' :: "'b => 'b => 'b" and one' :: "'b" and inv' :: "'b => 'b"
    and h :: "'a => 'b" +
  assumes map_closed: "x \<in> G \<Longrightarrow> h x \<in> H"
    and map_mult: "\<lbrakk>x \<in> G; y \<in> G\<rbrakk> \<Longrightarrow> h (mult x y) = mult' (h x) (h y)"
begin

lemma map_one:
  "h one = one'"
proof -
  have h_one_closed: "h one \<in> H"
    using G.one_closed by (rule map_closed)
  have h_one_idem: "h one = mult' (h one) (h one)"
  proof -
    have "h one = h (mult one one)"
      using G.one_closed by (simp add: G.mult_one_left)
    also have "... = mult' (h one) (h one)"
      using G.one_closed G.one_closed by (rule map_mult)
    finally show ?thesis .
  qed
  have "mult' one' (h one) = mult' (h one) (h one)"
    using h_one_closed h_one_idem by (simp add: H.mult_one_left)
  then have "one' = h one"
    by (rule H.right_cancel[OF h_one_closed H.one_closed h_one_closed])
  then show ?thesis
    by simp
qed

lemma map_inv:
  assumes x: "x \<in> G"
  shows "h (inv x) = inv' (h x)"
proof -
  have hx: "h x \<in> H"
    using x by (rule map_closed)
  have hinvx: "h (inv x) \<in> H"
    using x G.inv_closed[OF x] by (auto intro: map_closed)
  have eq_left: "mult' (h x) (h (inv x)) = one'"
  proof -
    have "h (mult x (inv x)) = mult' (h x) (h (inv x))"
      using x G.inv_closed[OF x] by (rule map_mult)
    then have "mult' (h x) (h (inv x)) = h (mult x (inv x))"
      by simp
    also have "... = h one"
      using x by (simp add: G.mult_inv_right)
    also have "... = one'"
      by (rule map_one)
    finally show ?thesis .
  qed
  have eq: "mult' (h x) (h (inv x)) = mult' (h x) (inv' (h x))"
    using eq_left hx by (simp add: H.mult_inv_right)
  show ?thesis
    by (rule H.left_cancel[OF hx hinvx H.inv_closed[OF hx] eq])
qed

end

end
