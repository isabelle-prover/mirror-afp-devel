section {* Miscellaneous Lemmas *}
theory Sep_Misc
imports Main "../../Automatic_Refinement/Lib/Misc"
begin
  text {* These lemmas are candidates to be pushed into the Isabelle/HOL 
    standard libraries *}

lemma imp_mp_iff[simp]: "a \<and> (a \<longrightarrow> b) \<longleftrightarrow> a \<and> b" 
  by metis

text {* The following lemma is useful to split non-empty lists. *}  
lemma list_not_emptyE: 
  assumes "l\<noteq>[]"
  obtains x xs where "l=x#xs" 
  using assms by (metis list.exhaust)

(* TODO: Move to Misc. Even to HOL/Product_Type? *)
definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" where
  "uncurry f \<equiv> \<lambda>(a,b). f a b"

lemma uncurry_apply[simp]: "uncurry f (a,b) = f a b"
  unfolding uncurry_def
  by simp

lemma curry_uncurry_id[simp]: "curry (uncurry f) = f"
  unfolding uncurry_def
  by simp

lemma uncurry_curry_id[simp]: "uncurry (curry f) = f"
  unfolding uncurry_def
  by simp

lemma do_curry: "f (a,b) = curry f a b" by simp
lemma do_uncurry: "f a b = uncurry f (a,b)" by simp

abbreviation "uncurry2 f \<equiv> uncurry (uncurry f)"
abbreviation "curry2 f \<equiv> curry (curry f)"

lemma do_curry2: "f ((a,b),c) = curry2 f a b c" by simp
lemma do_uncurry2: "f a b c = uncurry2 f ((a,b),c)" by simp



  (* TODO: Do not add to simpset. (Done in Misc) *)
  declare Misc.map_upd_eq_restrict[simp del]

  (* TODO: Move, analogous to List.length_greater_0_conv *) 
  lemma length_ge_1_conv[iff]: "Suc 0 \<le> length l \<longleftrightarrow> l\<noteq>[]"
    by (cases l) auto

  (* TODO: Move to Misc *)
  lemma (in -) min_less_self_conv[simp]: 
    "min a b < a \<longleftrightarrow> b < (a::_::linorder)" 
    "min a b < b \<longleftrightarrow> a < (b::_::linorder)" 
    by (auto simp: min_def)


  (* TODO: Move to Misc *)
  lemma ran_nth_set_encoding_conv[simp]: 
    "ran (\<lambda>i. if i<length l then Some (l!i) else None) = set l"
    apply safe
    apply (auto simp: ran_def split: split_if_asm) []
    apply (auto simp: in_set_conv_nth intro: ranI) []
    done

  lemma nth_image_indices[simp]: "op ! l ` {0..<length l} = set l"
    by (auto simp: in_set_conv_nth)

  (* TODO: Move *)  
  lemma nth_update_invalid[simp]:"\<not>i<length l \<Longrightarrow> l[j:=x]!i = l!i"  
    apply (induction l arbitrary: i j)
    apply (auto split: nat.splits)
    done

  lemma nth_list_update': "l[i:=x]!j = (if i=j \<and> i<length l then x else l!j)"  
    by auto

  lemma distinct_butlast_swap[simp]: 
    "distinct pq \<Longrightarrow> distinct (butlast (pq[i := last pq]))"
    apply (cases pq rule: rev_cases)
    apply (auto simp: list_update_append distinct_list_update split: nat.split)
    done

  (* TODO: Move *)  
  lemma last_take_nth_conv: "n \<le> length l \<Longrightarrow> n\<noteq>0 \<Longrightarrow> last (take n l) = l!(n - 1)"
    apply (induction l arbitrary: n)
    apply (auto simp: take_Cons split: nat.split)
    done





end
