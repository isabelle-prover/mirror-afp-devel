(*  Title:      Containers/Mapping_Impl.thy
    Author:     Andreas Lochbihler, KIT *)

theory Mapping_Impl imports 
  RBT_Mapping2
  AssocList
  "~~/src/HOL/Library/Mapping"
  Set_Impl
begin

section {* Different implementations of maps *}

code_modulename SML
  Mapping Mapping_Impl
  Mapping_Impl Mapping_Impl

definition map_impl_unsupported_operation :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a"
where [simp, code del]: "map_impl_unsupported_operation f = f ()"

code_abort "map_impl_unsupported_operation"

subsection {* Map implementations *}

definition Assoc_List_Mapping :: "('a, 'b) alist \<Rightarrow> ('a, 'b) mapping"
where [simp]: "Assoc_List_Mapping al = Mapping.Mapping (DAList.lookup al)"

definition RBT_Mapping :: "('a :: corder, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping"
where [simp]: "RBT_Mapping t = Mapping.Mapping (RBT_Mapping2.lookup t)"

code_datatype Assoc_List_Mapping RBT_Mapping Mapping

subsection {* Map operations *}

lemma [code, code del]: "Mapping.lookup = Mapping.lookup" ..

lemma lookup_Mapping_code [code]:
  "Mapping.lookup (Assoc_List_Mapping al) = DAList.lookup al"
  "Mapping.lookup (RBT_Mapping t) = RBT_Mapping2.lookup t"
by(simp_all)(transfer, rule)+

lemma [code, code del]: "Mapping.is_empty = Mapping.is_empty" ..

lemma is_empty_transfer [transfer_rule]:
  "(pcr_mapping op = op = ===> op =) (\<lambda>m. m = empty) Mapping.is_empty"
unfolding mapping.pcr_cr_eq
apply(rule fun_relI)
apply(case_tac y)
apply(simp add: Mapping.is_empty_def cr_mapping_def Mapping_inverse Mapping.keys.rep_eq)
done

lemma is_empty_Mapping [code]:
  fixes t :: "('a :: corder, 'b) mapping_rbt" shows
  "Mapping.is_empty (Assoc_List_Mapping al) \<longleftrightarrow> al = DAList.empty"
  "Mapping.is_empty (RBT_Mapping t) \<longleftrightarrow>
  (case ID CORDER('a) of None \<Rightarrow> map_impl_unsupported_operation (\<lambda>_. Mapping.is_empty (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping2.is_empty t)"
apply(simp_all split: option.split)
 apply(transfer, case_tac al, simp_all)
apply(transfer, simp)
done

lemma [code, code del]: "Mapping.update = Mapping.update" ..

lemma update_Mapping [code]:
  fixes t :: "('a :: corder, 'b) mapping_rbt" shows
  "Mapping.update k v (Mapping m) = Mapping (m(k \<mapsto> v))"
  "Mapping.update k v (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.update k v al)"
  "Mapping.update k v (RBT_Mapping t) =
  (case ID CORDER('a) of None \<Rightarrow> map_impl_unsupported_operation (\<lambda>_. Mapping.update k v (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.insert k v t))" (is ?RBT)
by(simp_all split: option.split)(transfer, simp)+

lemma [code, code del]: "Mapping.delete = Mapping.delete" ..

lemma delete_Mapping [code]:
  fixes t :: "('a :: corder, 'b) mapping_rbt" shows
  "Mapping.delete k (Mapping m) = Mapping (m(k := None))"
  "Mapping.delete k (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.delete k al)"
  "Mapping.delete k (RBT_Mapping t) = 
  (case ID CORDER('a) of None \<Rightarrow> map_impl_unsupported_operation (\<lambda>_. Mapping.delete k (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.delete k t))"
by(simp_all split: option.split)(transfer, simp)+

lemma [code, code del]: "Mapping.keys = Mapping.keys" ..

theorem (in ord) rbt_lookup_map_const: "rbt_lookup (RBT_Impl.map (\<lambda>_. f) t) = Option.map f \<circ> rbt_lookup t"
by(induct t)(simp_all add: fun_eq_iff)

lemma keys_Mapping [code]:
  fixes t :: "('a :: corder, 'b) mapping_rbt" shows
  "Mapping.keys (Mapping m) = Collect (\<lambda>k. m k \<noteq> None)" (is "?Mapping")
  "Mapping.keys (Assoc_List_Mapping al) = AssocList.keys al" (is "?Assoc_List")
  "Mapping.keys (RBT_Mapping t) = RBT_set (RBT_Mapping2.map (\<lambda>_ _. ()) t)" (is "?RBT")
proof -
  show ?Mapping by transfer auto
  show ?Assoc_List by simp(transfer, auto intro: rev_image_eqI)
  show ?RBT
    by(simp add: RBT_set_def)(transfer, auto simp add: ord.rbt_lookup_map_const o_def)
qed

lemma [code, code del]: "Mapping.size = Mapping.size" ..

lemma Mapping_size_transfer [transfer_rule]:
  "(pcr_mapping op = op = ===> op =) (card \<circ> dom) Mapping.size"
apply(rule fun_relI)
apply(case_tac y)
apply(simp add: Mapping.size_def Mapping.keys.rep_eq Mapping_inverse mapping.pcr_cr_eq cr_mapping_def)
done

lemma size_Mapping [code]:
  fixes t :: "('a :: corder, 'b) mapping_rbt" shows
  "Mapping.size (Assoc_List_Mapping al) = size al"
  "Mapping.size (RBT_Mapping t) =
  (case ID CORDER('a) of None \<Rightarrow> map_impl_unsupported_operation (\<lambda>_. Mapping.size (RBT_Mapping t))
                     | Some _ \<Rightarrow> length (RBT_Mapping2.entries t))"
apply(simp_all split: option.split)
apply(transfer, simp add: dom_map_of_conv_image_fst set_map[symmetric] distinct_card del: set_map)
apply transfer
apply(clarsimp simp add: size_eq_card_dom_lookup)
apply(simp add: linorder.rbt_lookup_keys[OF ID_corder] ord.is_rbt_rbt_sorted RBT_Impl.keys_def distinct_card linorder.distinct_entries[OF ID_corder] del: set_map)
apply(subst distinct_card)
apply(rule linorder.distinct_entries[OF ID_corder], assumption)
apply(simp_all add: ord.is_rbt_rbt_sorted)
done


lemma [code, code del]: "Mapping.tabulate = Mapping.tabulate" ..

lemma tabulate_Mapping [code]:
  "Mapping.tabulate xs f = fold (\<lambda>k m. Mapping.update k (f k) m) xs Mapping.empty"
apply(rule sym)
apply transfer
apply(unfold tabulate_alt_def)
apply(induct_tac xs rule: rev_induct)
apply(auto simp add: fun_eq_iff restrict_map_def)
done

datatype mapping_impl = Mapping_IMPL
declare mapping_impl.eq.simps [code del]

definition mapping_Choose :: mapping_impl where [simp]: "mapping_Choose = Mapping_IMPL"
definition mapping_Assoc_List :: mapping_impl where [simp]: "mapping_Assoc_List = Mapping_IMPL"
definition mapping_RBT :: mapping_impl where [simp]: "mapping_RBT = Mapping_IMPL"
definition mapping_Mapping :: mapping_impl where [simp]: "mapping_Mapping = Mapping_IMPL"

code_datatype mapping_Choose mapping_Assoc_List mapping_RBT mapping_Mapping

definition mapping_empty_choose :: "('a, 'b) mapping" 
where [simp]: "mapping_empty_choose = Mapping.empty"

lemma mapping_empty_choose_code [code]:
  "(mapping_empty_choose :: ('a :: corder, 'b) mapping) =
   (case ID CORDER('a) of Some _  \<Rightarrow> RBT_Mapping RBT_Mapping2.empty
    | None \<Rightarrow> Assoc_List_Mapping DAList.empty)"
by(auto split: option.split simp add: DAList.lookup_empty[abs_def] Mapping.empty_def)

definition mapping_impl_choose2 :: "mapping_impl \<Rightarrow> mapping_impl \<Rightarrow> mapping_impl"
where [simp]: "mapping_impl_choose2 = (\<lambda>_ _. Mapping_IMPL)"

lemma mapping_impl_choose2_code [code]:
  "mapping_impl_choose2 x y = mapping_Choose"
  "mapping_impl_choose2 mapping_Mapping mapping_Mapping = mapping_Mapping"
  "mapping_impl_choose2 mapping_Assoc_List mapping_Assoc_List = mapping_Assoc_List"
  "mapping_impl_choose2 mapping_RBT mapping_RBT = mapping_RBT"
by(simp_all)

definition mapping_empty :: "mapping_impl \<Rightarrow> ('a, 'b) mapping"
where [simp]: "mapping_empty = (\<lambda>_. Mapping.empty)"

lemma mapping_empty_code [code]:
  "mapping_empty mapping_Choose = mapping_empty_choose"
  "mapping_empty mapping_Mapping = Mapping (\<lambda>_. None)"
  "mapping_empty mapping_Assoc_List = Assoc_List_Mapping DAList.empty"
  "mapping_empty mapping_RBT = RBT_Mapping RBT_Mapping2.empty"
by(simp_all add: Mapping.empty_def DAList.lookup_empty[abs_def])

subsection {* Type classes *}

class mapping_impl = 
  fixes mapping_impl :: "('a, mapping_impl) phantom"

syntax (input)
  "_MAPPING_IMPL" :: "type => logic"  ("(1MAPPING'_IMPL/(1'(_')))")

parse_translation {*
let
  fun mapping_impl_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "mapping_impl"} $
       (Syntax.const @{type_syntax phantom} $ ty $ Syntax.const @{type_syntax mapping_impl}))
    | mapping_impl_tr ts = raise TERM ("mapping_impl_tr", ts);
in [(@{syntax_const "_MAPPING_IMPL"}, K mapping_impl_tr)] end
*}

lemma [code, code del]: "Mapping.empty = Mapping.empty" ..

lemma Mapping_empty_code [code, code_unfold]: 
  "(Mapping.empty :: ('a :: mapping_impl, 'b) mapping) =
   mapping_empty (of_phantom MAPPING_IMPL('a))"
by simp

instantiation unit :: mapping_impl begin
definition "MAPPING_IMPL(unit) = Phantom(unit) mapping_Assoc_List"
instance ..
end

instantiation bool :: mapping_impl begin
definition "MAPPING_IMPL(bool) = Phantom(bool) mapping_Assoc_List"
instance ..
end

instantiation nat :: mapping_impl begin
definition "MAPPING_IMPL(nat) \<equiv> Phantom(nat) mapping_RBT"
instance ..
end

instantiation int :: mapping_impl begin
definition "MAPPING_IMPL(int) = Phantom(int) mapping_RBT"
instance ..
end

instantiation Enum.finite_1 :: mapping_impl begin
definition "MAPPING_IMPL(Enum.finite_1) = Phantom(Enum.finite_1) mapping_Assoc_List"
instance ..
end

instantiation Enum.finite_2 :: mapping_impl begin
definition "MAPPING_IMPL(Enum.finite_2) = Phantom(Enum.finite_2) mapping_Assoc_List"
instance ..
end

instantiation Enum.finite_3 :: mapping_impl begin
definition "MAPPING_IMPL(Enum.finite_3) = Phantom(Enum.finite_3) mapping_Assoc_List"
instance ..
end

instantiation integer :: mapping_impl begin
definition "MAPPING_IMPL(integer) = Phantom(integer) mapping_RBT"
instance ..
end

instantiation natural :: mapping_impl begin
definition "MAPPING_IMPL(natural) = Phantom(natural) mapping_RBT"
instance ..
end

instantiation nibble :: mapping_impl begin
definition "MAPPING_IMPL(nibble) = Phantom(nibble) mapping_Assoc_List"
instance ..
end

instantiation char :: mapping_impl begin
definition "MAPPING_IMPL(char) = Phantom(char) mapping_RBT"
instance ..
end

instantiation sum :: (mapping_impl, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a + 'b) = Phantom('a + 'b) 
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"
instance ..
end

instantiation prod :: (mapping_impl, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a * 'b) = Phantom('a * 'b) 
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"
instance ..
end

instantiation list :: (type) mapping_impl begin
definition "MAPPING_IMPL('a list) = Phantom('a list) mapping_Choose"
instance ..
end

instantiation String.literal :: mapping_impl begin
definition "MAPPING_IMPL(String.literal) = Phantom(String.literal) mapping_RBT"
instance ..
end

instantiation option :: (mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a option) = Phantom('a option) (of_phantom MAPPING_IMPL('a))"
instance ..
end

instantiation set :: (type) mapping_impl begin
definition "MAPPING_IMPL('a set) = Phantom('a set) mapping_Choose"
instance ..
end

instantiation phantom :: (type, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL(('a, 'b) phantom) = Phantom (('a, 'b) phantom) 
  (of_phantom MAPPING_IMPL('b))"
instance ..
end

end