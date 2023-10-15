\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport for HOL Type Definitions\<close>
theory Transport_Typedef_Base
  imports
    HOL_Alignment_Binary_Relations
    Transport_Bijections
    HOL.Typedef
begin

context type_definition
begin

abbreviation (input) "L :: 'a \<Rightarrow> 'a \<Rightarrow> bool \<equiv> (=\<^bsub>A\<^esub>)"
abbreviation (input) "R :: 'b \<Rightarrow> 'b \<Rightarrow> bool \<equiv> (=)"

sublocale transport? :
  transport_eq_restrict_bijection "mem_of A" "\<top> :: 'b \<Rightarrow> bool" Abs Rep
  rewrites "(=\<^bsub>mem_of A\<^esub>) \<equiv> L"
  and "(=\<^bsub>\<top> :: 'b \<Rightarrow> bool\<^esub>) \<equiv> R"
  and "(galois_rel.Galois (=) (=) Rep)\<restriction>\<^bsub>mem_of A\<^esub>\<upharpoonleft>\<^bsub>\<top> :: 'b \<Rightarrow> bool\<^esub> \<equiv>
    (galois_rel.Galois (=) (=) Rep)"
  using Abs_inverse Rep_inverse
  by (intro transport_eq_restrict_bijection.intro bijection_onI)
  (auto simp: restrict_right_eq
    intro!: eq_reflection galois_rel.left_GaloisI Rep
    elim: galois_rel.left_GaloisE)

interpretation galois L R Abs Rep .

lemma Rep_left_Galois_self: "Rep y \<^bsub>L\<^esub>\<lessapprox> y"
  using Rep by (intro left_GaloisI) auto

definition "AR x y \<equiv> x = Rep y"

lemma left_Galois_eq_AR: "left_Galois = AR"
  unfolding AR_def
  by (auto intro!: galois_rel.left_GaloisI Rep elim: galois_rel.left_GaloisE)

end


end
