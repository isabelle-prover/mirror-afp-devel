(*  Title:      Containers/Mapping_Impl.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Mapping_Impl imports 
  RBT_Mapping2
  AssocList
  "HOL-Library.Mapping"
  Set_Impl
  Containers_Generator
begin

section \<open>Different implementations of maps\<close>

subsection \<open>Map implementations\<close>

definition Assoc_List_Mapping :: "('a, 'b) alist \<Rightarrow> ('a, 'b) mapping"
where [simp]: "Assoc_List_Mapping al = Mapping.Mapping (DAList.lookup al)"

definition RBT_Mapping :: "('a :: ccompare, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping"
where [simp]: "RBT_Mapping t = Mapping.Mapping (RBT_Mapping2.lookup t)"

code_datatype Assoc_List_Mapping RBT_Mapping Mapping

subsection \<open>Map operations\<close>

lemma lookup_Mapping_code [code, no_atp]:
  "Mapping.lookup (RBT_Mapping t) = RBT_Mapping2.lookup t"
  "Mapping.lookup (Assoc_List_Mapping al) = DAList.lookup al"
by(simp_all)(transfer, rule)+

lemma is_empty_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_mapping (=) (=) ===> (=)) (\<lambda>m. m = Map.empty) Mapping.is_empty"
unfolding mapping.pcr_cr_eq
apply(rule rel_funI)
apply(case_tac y)
apply(simp add: Mapping.is_empty_def cr_mapping_def Mapping_inverse Mapping.keys.rep_eq)
done

lemma is_empty_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.is_empty (RBT_Mapping t) \<longleftrightarrow>
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''is_empty RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.is_empty (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping2.is_empty t)"
  "Mapping.is_empty (Assoc_List_Mapping al) \<longleftrightarrow> al = DAList.empty"
apply(simp_all split: option.split)
 apply(transfer, case_tac al, simp_all)
apply(transfer, simp)
done

lemma update_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.update k v (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''update RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.update k v (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.insert k v t))" (is ?RBT)
  "Mapping.update k v (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.update k v al)"
  "Mapping.update k v (Mapping m) = Mapping (m(k \<mapsto> v))"
by(simp_all split: option.split)(transfer, simp)+

lemma delete_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.delete k (RBT_Mapping t) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''delete RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.delete k (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.delete k t))"
  "Mapping.delete k (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.delete k al)"
  "Mapping.delete k (Mapping m) = Mapping (m(k := None))"
by(simp_all split: option.split)(transfer, simp)+

theorem rbt_comp_lookup_map_const: "rbt_comp_lookup c (RBT_Impl.map (\<lambda>_. f) t) = map_option f \<circ> rbt_comp_lookup c t"
by(induct t)(auto simp: fun_eq_iff split: order.split)

lemma keys_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.keys (RBT_Mapping t) = RBT_set (RBT_Mapping2.map (\<lambda>_ _. ()) t)" (is "?RBT")
  "Mapping.keys (Assoc_List_Mapping al) = AssocList.keys al" (is "?Assoc_List")
  "Mapping.keys (Mapping m) = Collect (\<lambda>k. m k \<noteq> None)" (is "?Mapping")
proof -
  show ?Mapping by transfer auto
  show ?Assoc_List by simp(transfer, auto intro: rev_image_eqI)
  show ?RBT
    by(simp add: RBT_set_def, transfer, auto simp add: rbt_comp_lookup_map_const o_def)
qed

lemma Mapping_size_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_mapping (=) (=) ===> (=)) (card \<circ> dom) Mapping.size"
apply(rule rel_funI)
apply(case_tac y)
apply(simp add: Mapping.size_def Mapping.keys.rep_eq Mapping_inverse mapping.pcr_cr_eq cr_mapping_def)
done

lemma size_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.size (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''size RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.size (RBT_Mapping t))
                     | Some _ \<Rightarrow> length (RBT_Mapping2.entries t))"
  "Mapping.size (Assoc_List_Mapping al) = size al"
  subgoal
    apply (simp split: option.split)
    apply transfer
    apply (clarsimp simp add: size_eq_card_dom_lookup)
    apply (simp add: linorder.rbt_lookup_keys [OF ID_ccompare] ord.is_rbt_rbt_sorted RBT_Impl.keys_def distinct_card linorder.distinct_entries [OF ID_ccompare] flip: set_map)
    done
  subgoal
    apply simp
    apply transfer
    apply (simp add: dom_map_of_conv_image_fst distinct_card flip: set_map)
    done
  done

declare tabulate_fold [code]

declare ordered_keys_def [code]

declare Mapping.lookup_default_def [code]

lemma filter_code [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.filter P (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''filter RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.filter P (RBT_Mapping t))
                         | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.filter (\<lambda>(k, v). P k v) t))"
  "Mapping.filter P (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.filter (\<lambda>(k, v). P k v) al)"
  "Mapping.filter P (Mapping m) = Mapping (\<lambda>k. case m k of None \<Rightarrow> None | Some v \<Rightarrow> if P k v then Some v else None)"
  subgoal by(clarsimp simp add: Mapping_inject Mapping.filter.abs_eq fun_eq_iff split: option.split)
  subgoal by (simp, transfer)(simp add: map_of_filter_apply fun_eq_iff cong: if_cong option.case_cong)
  subgoal by transfer simp
  done

lemma map_values_code [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.map_values f (RBT_Mapping t) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''map_values RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.map_values f (RBT_Mapping t))
                         | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.map f t))"
  "Mapping.map_values f (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.map_values f al)"
  "Mapping.map_values f (Mapping m) = Mapping (\<lambda>k. map_option (f k) (m k))"
  subgoal by (clarsimp simp add: Mapping_inject Mapping.map_values.abs_eq fun_eq_iff split: option.split)
  subgoal by (simp, transfer) (simp add: fun_eq_iff map_of_map')
  subgoal by transfer simp
  done

lemma bulkload_code [code]:
  "Mapping.bulkload vs = RBT_Mapping (RBT_Mapping2.bulkload (zip_with_index vs))"
  by (simp add: Mapping.bulkload.abs_eq Mapping_inject ccompare_nat_def ID_def fun_eq_iff)

datatype mapping_impl = Mapping_IMPL

lemma [code]:
  fixes x :: mapping_impl
  shows "size x = 0"
  and "size_mapping_impl x = 0"
  subgoal by (cases x) simp
  subgoal by (cases x) simp
  done

definition mapping_Choose :: mapping_impl
  where [simp]: "mapping_Choose = Mapping_IMPL"

definition mapping_Assoc_List :: mapping_impl
  where [simp]: "mapping_Assoc_List = Mapping_IMPL"

definition mapping_RBT :: mapping_impl
  where [simp]: "mapping_RBT = Mapping_IMPL"

definition mapping_Mapping :: mapping_impl
  where [simp]: "mapping_Mapping = Mapping_IMPL"

code_datatype mapping_Choose mapping_Assoc_List mapping_RBT mapping_Mapping

definition mapping_empty_choose :: "('a, 'b) mapping" 
  where [simp]: "mapping_empty_choose = Mapping.empty"

lemma mapping_empty_choose_code [code]:
  "(mapping_empty_choose :: ('a :: ccompare, 'b) mapping) =
   (case ID CCOMPARE('a) of Some _  \<Rightarrow> RBT_Mapping RBT_Mapping2.empty
    | None \<Rightarrow> Assoc_List_Mapping DAList.empty)"
  by (auto split: option.split simp add: DAList.lookup_empty [abs_def] Mapping.empty_def)

definition mapping_impl_choose2 :: "mapping_impl \<Rightarrow> mapping_impl \<Rightarrow> mapping_impl"
  where [simp]: "mapping_impl_choose2 = (\<lambda>_ _. Mapping_IMPL)"

lemma mapping_impl_choose2_code [code]:
  "mapping_impl_choose2 mapping_RBT mapping_RBT = mapping_RBT"
  "mapping_impl_choose2 mapping_Assoc_List mapping_Assoc_List = mapping_Assoc_List"
  "mapping_impl_choose2 mapping_Mapping mapping_Mapping = mapping_Mapping"
  "mapping_impl_choose2 x y = mapping_Choose"
  by simp_all

definition mapping_empty :: "mapping_impl \<Rightarrow> ('a, 'b) mapping"
  where [simp]: "mapping_empty = (\<lambda>_. Mapping.empty)"

lemma mapping_empty_code [code]:
  "mapping_empty mapping_RBT = RBT_Mapping RBT_Mapping2.empty"
  "mapping_empty mapping_Assoc_List = Assoc_List_Mapping DAList.empty"
  "mapping_empty mapping_Mapping = Mapping (\<lambda>_. None)"
  "mapping_empty mapping_Choose = mapping_empty_choose"
  by (simp_all add: Mapping.empty_def DAList.lookup_empty [abs_def])


subsection \<open>Type classes\<close>

class mapping_impl = 
  fixes mapping_impl :: "('a, mapping_impl) phantom"

syntax (input)
  "_MAPPING_IMPL" :: "type => logic"  (\<open>(1MAPPING'_IMPL/(1'(_')))\<close>)

syntax_consts
  "_MAPPING_IMPL" == mapping_impl

parse_translation \<open>
let
  fun mapping_impl_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "mapping_impl"} $
       (Syntax.const @{type_syntax phantom} $ ty $ Syntax.const @{type_syntax mapping_impl}))
    | mapping_impl_tr ts = raise TERM ("mapping_impl_tr", ts);
in [(@{syntax_const "_MAPPING_IMPL"}, K mapping_impl_tr)] end
\<close>

lemma Mapping_empty_code [code, code_unfold]: 
  "(Mapping.empty :: ('a :: mapping_impl, 'b) mapping) =
   mapping_empty (of_phantom MAPPING_IMPL('a))"
by simp


subsection \<open>Generator for the @{class mapping_impl}-class\<close>

text \<open>
This generator registers itself at the derive-manager for the classes @{class mapping_impl}.
Here, one can choose
the desired implementation via the parameter. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (rbt,assoclist,mapping,choose, or arbitrary constant name) mapping-impl}
\end{itemize}
\<close>


text \<open>
This generator can be used for arbitrary types, not just datatypes. 
\<close>

ML_file \<open>mapping_impl_generator.ML\<close> 

derive (assoclist) mapping_impl unit bool
derive (rbt) mapping_impl nat
derive (mapping_RBT) mapping_impl int (* shows usage of constant names *)
derive (assoclist) mapping_impl Enum.finite_1 Enum.finite_2 Enum.finite_3
derive (rbt) mapping_impl integer natural
derive (rbt) mapping_impl char

instantiation sum :: (mapping_impl, mapping_impl) mapping_impl
begin

definition "MAPPING_IMPL('a + 'b) = Phantom('a + 'b)
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"

instance ..

end

instantiation prod :: (mapping_impl, mapping_impl) mapping_impl begin

definition "MAPPING_IMPL('a * 'b) = Phantom('a * 'b)
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"

instance ..

end

derive (choose) mapping_impl list
derive (rbt) mapping_impl String.literal

instantiation option :: (mapping_impl) mapping_impl 
begin

definition "MAPPING_IMPL('a option) = Phantom('a option) (of_phantom MAPPING_IMPL('a))"

instance ..

end

derive (choose) mapping_impl set

instantiation phantom :: (type, mapping_impl) mapping_impl
begin

definition "MAPPING_IMPL(('a, 'b) phantom) = Phantom (('a, 'b) phantom)
  (of_phantom MAPPING_IMPL('b))"

instance ..

end

declare [[code drop:
  rec_mapping_impl
  case_mapping_impl
  \<open>HOL.equal :: mapping_impl \<Rightarrow> _\<close>
  Mapping.combine_with_key
  Mapping.combine
  ]]

code_identifier
  code_module Mapping \<rightharpoonup> (SML) Mapping_Impl
| code_module Mapping_Impl \<rightharpoonup> (SML) Mapping_Impl

end
