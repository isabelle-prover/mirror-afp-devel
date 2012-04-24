header {* \isaheader{Maps from Naturals by Arrays} *}
theory ArrayMapImpl
imports 
  "../spec/MapSpec"
  "../gen_algo/MapGA"
  "../common/Array"
begin
  text_raw {*\label{thy:ArrayMapImpl}*}

(*@impl Map
  @type 'v iam
  @abbrv iam,im
  Maps of natural numbers implemented by arrays.
*)

  type_synonym 'v iam = "'v option array"

  subsection {* Definitions *}

  definition iam_\<alpha> :: "'v iam \<Rightarrow> nat \<rightharpoonup> 'v" where
    "iam_\<alpha> a i \<equiv> if i < array_length a then array_get a i else None"

  abbreviation iam_invar :: "'v iam \<Rightarrow> bool" where "iam_invar \<equiv> \<lambda>_. True"

  definition iam_empty :: "unit \<Rightarrow> 'v iam" 
    where "iam_empty \<equiv> \<lambda>_::unit. array_of_list []"

  definition iam_lookup :: "nat \<Rightarrow> 'v iam \<rightharpoonup> 'v"
    where "iam_lookup k a \<equiv> iam_\<alpha> a k"

  definition "iam_increment (l::nat) idx \<equiv> 
    max (idx + 1 - l) (2 * l + 3)"

  lemma incr_correct: "\<not> idx < l \<Longrightarrow> idx < l + iam_increment l idx"
    unfolding iam_increment_def by auto

  definition iam_update :: "nat \<Rightarrow> 'v \<Rightarrow> 'v iam \<Rightarrow> 'v iam"
    where "iam_update k v a \<equiv> let
    l = array_length a;
    a = if k < l then a else array_grow a (iam_increment l k) None
  in
    array_set a k (Some v)
    "

  definition "iam_update_dj \<equiv> iam_update"

  definition iam_delete :: "nat \<Rightarrow> 'v iam \<Rightarrow> 'v iam"
    where "iam_delete k a \<equiv> 
    if k<array_length a then array_set a k None else a"

  fun iam_iteratei_aux 
    :: "nat \<Rightarrow> ('v iam) \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> (nat \<times> 'v\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>" 
    where
      "iam_iteratei_aux 0 a c f \<sigma> = \<sigma>"
    | "iam_iteratei_aux i a c f \<sigma> = (
        if c \<sigma> then   
          iam_iteratei_aux (i - 1) a c f (
            case array_get a (i - 1) of None \<Rightarrow> \<sigma> | Some x \<Rightarrow> f (i - 1, x) \<sigma>
          )
        else \<sigma>)"

  definition iam_iteratei :: "'v iam \<Rightarrow> (nat \<times> 'v,'\<sigma>) set_iterator" where 
    "iam_iteratei a = iam_iteratei_aux (array_length a) a"

  definition "iam_add == it_add iam_update iam_iteratei"
  definition "iam_add_dj == iam_add"
  definition "iam_isEmpty == iti_isEmpty iam_iteratei"
  definition "iam_sel == iti_sel iam_iteratei"
  definition "iam_sel' = iti_sel_no_map iam_iteratei"

  definition "iam_to_list == it_map_to_list iam_iteratei"
  definition "list_to_iam == gen_list_to_map iam_empty iam_update"
  
subsection {* Correctness *}

lemmas iam_defs = 
  iam_\<alpha>_def
  iam_empty_def
  iam_lookup_def
  iam_update_def
  iam_update_dj_def
  iam_delete_def
  iam_iteratei_def
  iam_add_def
  iam_add_dj_def
  iam_isEmpty_def
  iam_sel_def
  iam_sel'_def
  iam_to_list_def
  list_to_iam_def


  lemma iam_empty_impl: "map_empty iam_\<alpha> iam_invar iam_empty"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_empty_def
    by auto

  interpretation iam!: map_empty iam_\<alpha> iam_invar iam_empty 
    using iam_empty_impl .

  lemma iam_lookup_impl: "map_lookup iam_\<alpha> iam_invar iam_lookup"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_lookup_def
    by auto
  interpretation iam!: map_lookup iam_\<alpha> iam_invar iam_lookup 
    using iam_lookup_impl .
  
  lemma array_get_set_iff: "i<array_length a \<Longrightarrow> 
    array_get (array_set a i x) j = (if i=j then x else array_get a j)"
    by (auto simp: array_get_array_set_other)

  lemma iam_update_impl: "map_update iam_\<alpha> iam_invar iam_update"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_update_def
    apply (rule ext)
    apply (auto simp: Let_def array_get_set_iff incr_correct)
    done
  interpretation iam!: map_update iam_\<alpha> iam_invar iam_update
    using iam_update_impl .

  lemma iam_update_dj_impl: "map_update_dj iam_\<alpha> iam_invar iam_update_dj"
    apply (unfold iam_update_dj_def) by (rule iam.update_dj_by_update)
  interpretation iam!: map_update_dj iam_\<alpha> iam_invar iam_update_dj
    using iam_update_dj_impl .

  lemma iam_delete_impl: "map_delete iam_\<alpha> iam_invar iam_delete"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_delete_def
    apply (rule ext)
    apply (auto simp: Let_def array_get_set_iff)
    done
  interpretation iam!: map_delete iam_\<alpha> iam_invar iam_delete 
    using iam_delete_impl .
  
  lemma iam_iteratei_aux_foldli_conv :
    "iam_iteratei_aux n a =
     foldli (List.map_filter (\<lambda>n. Option.map (\<lambda>v. (n, v)) (array_get a n)) (rev [0..<n]))"
  by (induct n) (auto simp add: List.map_filter_def fun_eq_iff)

  lemma iam_iteratei_foldli_conv :
    "iam_iteratei a =
     foldli (List.map_filter (\<lambda>n. Option.map (\<lambda>v. (n, v)) (array_get a n)) (rev [0..<(array_length a)]))"
    unfolding iam_iteratei_def iam_iteratei_aux_foldli_conv by simp

  lemma iam_iteratei_correct : 
  fixes m::"'a option array"
  defines "kvs \<equiv> List.map_filter (\<lambda>n. Option.map (\<lambda>v. (n, v)) (array_get m n)) (rev [0..<(array_length m)])"
  shows "map_iterator_rev_linord (iam_iteratei m) (iam_\<alpha> m)" 
  proof (rule map_iterator_rev_linord_I [of kvs])
    show "iam_iteratei m = foldli kvs"
      unfolding iam_iteratei_foldli_conv kvs_def by simp
  next
    def al \<equiv> "array_length m"
    show dist_kvs: "distinct (map fst kvs)" and "sorted (rev (map fst kvs))"
      unfolding kvs_def al_def[symmetric]
      apply (induct al)
      apply (simp_all add: List.map_filter_simps set_map_filter image_iff sorted_append
                      split: option.split)
    done

    from dist_kvs
    have "\<And>i. map_of kvs i = iam_\<alpha> m i"
      unfolding kvs_def 
      apply (case_tac "array_get m i")
      apply (simp_all add: iam_\<alpha>_def map_of_eq_None_iff set_map_filter image_iff)
    done
    thus "iam_\<alpha> m = map_of kvs" by auto 
  qed
 
  lemma iam_iteratei_rev_linord_impl: "map_reverse_iterateoi iam_\<alpha> iam_invar iam_iteratei"
    apply unfold_locales
    apply (simp add: iam_\<alpha>_def[abs_def] dom_def)
    apply (simp add: iam_iteratei_correct)
  done

  interpretation iam!: map_reverse_iterateoi iam_\<alpha> iam_invar iam_iteratei 
    using iam_iteratei_rev_linord_impl .
 
  lemma iam_iteratei_impl: "map_iteratei iam_\<alpha> iam_invar iam_iteratei"
    using MapGA.iti_by_ritoi [OF iam_iteratei_rev_linord_impl] .
  interpretation iam!: map_iteratei iam_\<alpha> iam_invar iam_iteratei 
    using iam_iteratei_impl .
  
  lemma iam_add_impl: "map_add iam_\<alpha> iam_invar iam_add"
    unfolding iam_add_def 
    using it_add_correct[OF iam_iteratei_impl iam_update_impl] .
  interpretation iam!: map_add iam_\<alpha> iam_invar iam_add using iam_add_impl .
  
  lemma iam_add_dj_impl: "map_add_dj iam_\<alpha> iam_invar iam_add_dj"
    unfolding iam_add_dj_def by (rule iam.add_dj_by_add)
  interpretation iam!: map_add_dj iam_\<alpha> iam_invar iam_add_dj 
    using iam_add_dj_impl .
  
  lemma iam_isEmpty_impl: "map_isEmpty iam_\<alpha> iam_invar iam_isEmpty"
    unfolding iam_isEmpty_def 
    using iti_isEmpty_correct[OF iam_iteratei_impl] .
  interpretation iam!: map_isEmpty iam_\<alpha> iam_invar iam_isEmpty 
    using iam_isEmpty_impl .

  lemma iam_sel_impl: "map_sel iam_\<alpha> iam_invar iam_sel"
    unfolding iam_sel_def 
    using iti_sel_correct[OF iam_iteratei_impl] .
  interpretation iam!: map_sel iam_\<alpha> iam_invar iam_sel
    using iam_sel_impl .

  lemma iam_sel'_impl: "map_sel' iam_\<alpha> iam_invar iam_sel'"
    unfolding iam_sel'_def 
    using iti_sel'_correct[OF iam_iteratei_impl] .
  interpretation iam!: map_sel' iam_\<alpha> iam_invar iam_sel'
    using iam_sel'_impl .

  lemma iam_to_list_impl: "map_to_list iam_\<alpha> iam_invar iam_to_list"
    unfolding iam_to_list_def 
    using it_map_to_list_correct[OF iam_iteratei_impl] .
  interpretation iam!: map_to_list iam_\<alpha> iam_invar iam_to_list
    using iam_to_list_impl .

  lemma list_to_iam_impl: "list_to_map iam_\<alpha> iam_invar list_to_iam"
    unfolding list_to_iam_def 
    using gen_list_to_map_correct[OF iam_empty_impl iam_update_impl] .
  interpretation iam!: list_to_map iam_\<alpha> iam_invar list_to_iam
    using list_to_iam_impl .
  
declare iam.finite[simp del, rule del]

lemmas iam_correct =
  iam.empty_correct
  iam.lookup_correct
  iam.update_correct
  iam.update_dj_correct
  iam.delete_correct
  iam.add_correct
  iam.add_dj_correct
  iam.isEmpty_correct
  iam.to_list_correct
  iam.to_map_correct

subsection "Code Generation"

export_code
  iam_empty
  iam_lookup
  iam_update
  iam_update_dj
  iam_delete
  iam_iteratei
  iam_add
  iam_add_dj
  iam_isEmpty
  iam_sel
  iam_sel'
  iam_to_list
  list_to_iam
  in SML
  module_name ArrayMap
  file -
    
end
