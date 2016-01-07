(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Preliminaries\<close>
subsection \<open>Missing Multiset\<close>

text \<open>This theory provides some definitions and lemmas on multisets which we did not find in the 
  Isabelle distribution.\<close>

theory Missing_Multiset
imports
  "~~/src/HOL/Library/Multiset"
begin


lemma msetprod_multiset_of[simp]: "msetprod (mset xs) = listprod xs"
  by (induct xs, auto simp: ac_simps) 

lemma multiset_subset_insert: "{ps. ps \<subseteq># xs + {#x#}} =
    {ps. ps \<subseteq># xs} \<union> (\<lambda>ps. ps + {#x#}) ` {ps. ps \<subseteq># xs}" (is "?l = ?r")
proof -
  {
    fix ps
    have "(ps \<in> ?l) = (ps \<subseteq># xs + {# x #})" by auto
    also have "\<dots> = (ps \<in> ?r)"
    proof (cases "x \<in># ps")
      case True
      then obtain qs where ps: "ps = qs + {#x#}" by (metis insert_DiffM2)
      show ?thesis unfolding ps mset_le_mono_add_right_cancel 
        by (auto simp: mset_le_insertD)
    next
      case False
      hence cx: "count ps x = 0" by auto
      hence id: "(ps \<subseteq># xs + {#x#}) = (ps \<subseteq># xs)"
        by (simp add: inter_add_left1 subset_mset.inf.absorb_iff2)
      show ?thesis unfolding id using False by auto
    qed
    finally have "(ps \<in> ?l) = (ps \<in> ?r)" .
  }
  thus ?thesis by auto
qed

lemma msetprod_zero: 
  "msetprod (xs :: 'a :: {comm_monoid_mult,zero_neq_one,semiring_no_zero_divisors} multiset) = 0 
    \<longleftrightarrow> (0 \<in> set_mset xs)"
  by (induct xs, auto)

lemma multiset_of_sublists: "mset ` set (sublists xs) = { ps. ps \<subseteq># mset xs}"
proof (induct xs)
  case (Cons x xs)
  show ?case (is "?l = ?r")
  proof -
    have id: "?r = {ps. ps \<subseteq># mset xs} \<union> (\<lambda> ps. ps + {#x#}) ` {ps. ps \<subseteq># mset xs}"
      by (simp add: multiset_subset_insert)
    show ?thesis unfolding id Cons[symmetric]
      by (auto simp add: Let_def) (metis UnCI image_iff mset.simps(2))
  qed
qed simp
end