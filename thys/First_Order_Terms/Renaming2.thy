(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)

subsection \<open>Rename names in two ways.\<close>

theory Renaming2
  imports 
    Fresh_Identifiers.Fresh
begin

typedef ('v :: infinite) renaming2 = "{ (v1 :: 'v \<Rightarrow> 'v, v2 :: 'v \<Rightarrow> 'v) | v1 v2. inj v1 \<and> inj v2 \<and> range v1 \<inter> range v2 = {} }" 
proof -
  let ?U = "UNIV :: 'v set" 
  have inf: "infinite ?U" by (rule infinite_UNIV)
  have "ordLeq3 (card_of ?U) (card_of ?U)" 
    using card_of_refl ordIso_iff_ordLeq by blast
  from card_of_Plus_infinite1[OF inf this, folded card_of_ordIso] 
  obtain f where bij: "bij_betw f (?U <+> ?U) ?U" by auto
  hence injf: "inj f" by (simp add: bij_is_inj)
  define v1 where "v1 = f o Inl" 
  define v2 where "v2 = f o Inr" 
  have inj: "inj v1" "inj v2" unfolding v1_def v2_def by (intro inj_compose[OF injf], auto)+
  have "range v1 \<inter> range v2 = {}" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain x where "v1 x = v2 x" 
      using injD injf v1_def v2_def by fastforce
    hence "f (Inl x) = f (Inr x)" unfolding v1_def v2_def by auto
    with injf show False unfolding inj_on_def by blast
  qed
  with inj show ?thesis by blast
qed

setup_lifting type_definition_renaming2

lift_definition rename_1 :: "'v :: infinite renaming2 \<Rightarrow> 'v \<Rightarrow> 'v" is fst .
lift_definition rename_2 :: "'v :: infinite renaming2 \<Rightarrow> 'v \<Rightarrow> 'v" is snd .

lemma rename_12: "inj (rename_1 r)" "inj (rename_2 r)" "range (rename_1 r) \<inter> range (rename_2 r) = {}" 
  by (transfer, auto)+

end
