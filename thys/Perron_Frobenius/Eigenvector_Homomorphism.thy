(*
  Author: R. Thiemann 
*)
section \<open>Homomorphism properties for eigenvalues and eigenvectors\<close>

theory Eigenvector_Homomorphism
imports 
  "$AFP/Jordan_Normal_Form/Spectral_Radius"
begin

(* TODO: move these facts into Char_Poly and Matrix *)

context semiring_hom
begin
lemma vec_hom_scalar_mult: "vec\<^sub>h (ev \<odot>\<^sub>v v) = hom ev \<odot>\<^sub>v vec\<^sub>h v"
  by (rule vec_eqI, auto)
end

context inj_ring_hom 
begin 

lemma eigenvector_hom: assumes A: "A \<in> carrier\<^sub>m n n"
  and ev: "eigenvector A v ev"
  shows "eigenvector (mat\<^sub>h A) (vec\<^sub>h v) (hom ev)"
proof -
  let ?A = "mat\<^sub>h A" 
  let ?v = "vec\<^sub>h v"
  let ?ev = "hom ev"
  from ev[unfolded eigenvector_def] A
  have v: "v \<in> carrier\<^sub>v n" "v \<noteq> \<zero>\<^sub>v n" "A \<otimes>\<^sub>m\<^sub>v v = ev \<odot>\<^sub>v v" by auto
  from v(1) have v1: "?v \<in> carrier\<^sub>v n" by simp
  from v(1-2) obtain i where "i < n" and "v $ i \<noteq> 0" by force
  with v(1) have "?v $ i \<noteq> 0" by auto
  hence v2: "?v \<noteq> \<zero>\<^sub>v n" using `i < n` v(1) by force
  from arg_cong[OF v(3), of "vec\<^sub>h", unfolded mat_vec_mult_hom[OF A v(1)] vec_hom_scalar_mult]
  have v3: "?A \<otimes>\<^sub>m\<^sub>v ?v = ?ev \<odot>\<^sub>v ?v" .
  from v1 v2 v3
  show ?thesis unfolding eigenvector_def using A by auto
qed

lemma eigenvalue_hom: assumes A: "A \<in> carrier\<^sub>m n n"
  and ev: "eigenvalue A ev"
  shows "eigenvalue (mat\<^sub>h A) (hom ev)"
  using eigenvector_hom[OF A, of _ ev] ev
  unfolding eigenvalue_def by auto

lemma eigenvector_hom_rev: assumes A: "A \<in> carrier\<^sub>m n n"
  and ev: "eigenvector (mat\<^sub>h A) (vec\<^sub>h v) (hom ev)"
  shows "eigenvector A v ev"
proof -
  let ?A = "mat\<^sub>h A" 
  let ?v = "vec\<^sub>h v"
  let ?ev = "hom ev"
  from ev[unfolded eigenvector_def] A
  have v: "v \<in> carrier\<^sub>v n" "?v \<noteq> \<zero>\<^sub>v n" "?A \<otimes>\<^sub>m\<^sub>v ?v = ?ev \<odot>\<^sub>v ?v" by auto
  from v(1-2) obtain i where "i < n" and "v $ i \<noteq> 0" by force
  with v(1) have "v $ i \<noteq> 0" by auto
  hence v2: "v \<noteq> \<zero>\<^sub>v n" using `i < n` v(1) by force
  from vec_hom_inj[OF v(3)[folded mat_vec_mult_hom[OF A v(1)] vec_hom_scalar_mult]]
  have v3: "A \<otimes>\<^sub>m\<^sub>v v = ev \<odot>\<^sub>v v" .
  from v(1) v2 v3
  show ?thesis unfolding eigenvector_def using A by auto
qed

end

end