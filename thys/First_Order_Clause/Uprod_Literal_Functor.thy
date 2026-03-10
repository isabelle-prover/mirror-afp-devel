theory Uprod_Literal_Functor
  imports Literal_Functor Uprod_Extra
begin

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "upair ` I \<TTurnstile>l Pos (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "upair ` I \<TTurnstile>l Neg (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps uprod_mem_image_iff_prod_mem[OF \<open>sym I\<close>]
  by simp_all

abbreviation Pos_Upair (infix "\<approx>" 66) where
  "Pos_Upair t t' \<equiv> Pos (Upair t t')"

abbreviation Neg_Upair (infix "!\<approx>" 66) where
  "Neg_Upair t t' \<equiv> Neg (Upair t t')"

abbreviation uprod_literal_to_set where "uprod_literal_to_set l \<equiv> \<Union>(set_uprod ` set_literal l)"

lemma uprod_literal_to_set_atm_of: "uprod_literal_to_set l = set_uprod (atm_of l)"
  by (cases l) auto

abbreviation map_uprod_literal where "map_uprod_literal f \<equiv> map_literal (map_uprod f)"  

global_interpretation uprod_literal_functor: non_empty_finite_natural_functor where
  map = map_uprod_literal and to_set = uprod_literal_to_set
  by unfold_locales (auto intro: literal.map_cong0 uprod.map_cong0)

global_interpretation uprod_literal_functor: natural_functor_conversion where
  map = map_uprod_literal and to_set = uprod_literal_to_set and map_to = map_uprod_literal and
  map_from = map_uprod_literal and map' = map_uprod_literal and to_set' = uprod_literal_to_set
  by unfold_locales auto

type_synonym 't atom = "'t uprod"

type_synonym 't clause = "'t atom clause"

end
