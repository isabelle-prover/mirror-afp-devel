subsection \<open>From Rensets to Nominal Sets\<close>

(* From substitutive sets satisfying finite support to nominal sets *)
theory Rensets_to_Nominal_Sets
imports Rensets Nominal_Sets 
begin

text \<open>This theory shows that any finitely supported rensets gives rise to a nominal set.
This is done by defining swapping from renaming. \<close>


context Renset_FinSupp
begin

(* Definition of the swapping operator: *)

definition swapA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" where 
  "swapA a z1 z2 \<equiv> 
 let yy = pickFreshA [z1,z2] [a] in
    vsubstA (vsubstA (vsubstA a yy z1) z1 z2) z2 yy"

lemma swapA: 
  "\<exists>yy. yy\<notin>{z1,z2} \<and> freshA yy a \<and> 
    swapA a z1 z2 = vsubstA (vsubstA (vsubstA a yy z1) z1 z2) z2 yy"
proof-
  define yy where yy: "yy = pickFreshA [z1, z2] [a]"
  have "swapA a z1 z2 = vsubstA (vsubstA (vsubstA a yy z1) z1 z2) z2 yy"
    unfolding swapA_def yy by (simp add: Let_def)
  moreover have "yy\<notin>{z1,z2} \<and> freshA yy a" using pickFreshA[of "[z1,z2]" "[a]" ] 
    unfolding yy by auto
  ultimately show ?thesis by auto
qed

(* Verifying the swappable set properties: *)

lemma swapA_id[simp]:
  "swapA a z z = a"
  using swapA[of z z] by (metis vsubstA_chain_freshA vsubstA_id)

lemma vvsubstA_twoWays:
  assumes "uu \<noteq> x \<and> uu \<noteq> y \<and> freshA uu a" "vv \<noteq> x \<and> vv \<noteq> y \<and> freshA vv a"
  shows "vsubstA (vsubstA (vsubstA a uu x) x y) y uu = 
       vsubstA (vsubstA (vsubstA a vv x) x y) y vv"
  by (smt (verit, best) vsubstA_id vsubstA_idem vsubstA_chain vsubstA_commute_diff 
      assms vsubstA_chain_freshA)

lemma swapA_any:
  assumes "uu \<noteq> x \<and> uu \<noteq> y \<and> freshA uu a"
  shows "swapA a x y = vsubstA (vsubstA (vsubstA a uu x) x y) y uu"
  by (metis assms insertCI swapA vvsubstA_twoWays)

lemma swapA_invol[simp]: "swapA (swapA a x y) x y = a"
proof(cases "x = y")
  case True
  thus ?thesis by simp
next
  case False
  obtain yy where yy: "yy \<noteq> x \<and> yy \<noteq> y \<and> freshA yy a" 
    and 0: "swapA a x y = vsubstA (vsubstA (vsubstA a yy x) x y) y yy"
    using swapA[of x y] by auto 
  define dd where "dd \<equiv> vsubstA (vsubstA (vsubstA a yy x) x y) y yy"

  have "finite ({vv. \<not> freshA vv a} \<union> {yy,x,y})"  
  	by (simp add: cofinite_freshA)
  then obtain vv where vv: "vv \<noteq> yy \<and> vv \<noteq> x \<and> vv \<noteq> y \<and> freshA vv a" 
    by (metis (no_types, lifting) UnCI exists_var insertCI mem_Collect_eq)

  have 11: "swapA dd x y = vsubstA (vsubstA (vsubstA dd vv x) x y) y vv"
    using swapA_any dd_def freshA_vsubstA vv by auto

  show ?thesis using yy vv unfolding 0 11[unfolded dd_def] 
    using vsubstA_commute_diff 
    by (smt (z3) freshA_vsubstA2 vsubstA_chain_freshA vsubstA_id)
qed

lemma swapA_cmp: 
  "swapA (swapA a x y) z1 z2 = swapA (swapA a z1 z2) (sw x z1 z2) (sw y z1 z2)"
proof(cases "z1=z2 \<or> x = y")
  case True
  thus ?thesis by auto
next
  case False
  have "finite ({uu. \<not> freshA uu a} \<union> {z1,z2,x,y})"  
  	by (simp add: cofinite_freshA)
  then obtain uu where uu: "uu \<noteq> z1 \<and> uu \<noteq> z2 \<and> uu \<noteq> x \<and> uu \<noteq> y \<and> freshA uu a" 
    by (metis (no_types, lifting) UnCI exists_var insertCI mem_Collect_eq)
      (* *)
  have "finite ({uu'. \<not> freshA uu' a} \<union> {z1,z2,x,y,uu})"  
  	by (simp add: cofinite_freshA)
  then obtain uu' where uu': "uu' \<noteq> z1 \<and> uu' \<noteq> z2 \<and> uu' \<noteq> x \<and> uu' \<noteq> y \<and> uu' \<noteq> uu \<and> freshA uu' a" 
    by (smt (z3) UnCI exists_var insertCI mem_Collect_eq)
      (* *)

  show ?thesis apply(subst swapA_any[of uu])
    subgoal using uu by auto
    subgoal apply(subst swapA_any[of uu'])
      subgoal using uu' by (simp add: freshA_vsubstA2)
      subgoal apply(subst swapA_any[of uu])
        subgoal using uu by (simp add: freshA_vsubstA2)
        subgoal apply(subst swapA_any[of uu'])
          subgoal using uu' by (simp add: freshA_vsubstA2 sw_def)
          subgoal apply(cases "x = z1", simp_all)
            subgoal apply(cases "y = z1", simp_all)
              subgoal   
              	by (smt (verit, ccfv_threshold) vsubstA_id vsubstA_idem 
                    vsubstA_chain vsubstA_commute_diff swapA_any uu uu')  
              subgoal apply(cases "y = z2", simp_all)
                subgoal by (smt (z3) uu uu' vsubstA_chain vsubstA_chain_freshA vsubstA_commute_diff)
                subgoal by (smt (z3) freshA_vsubstA2 uu uu' vsubstA_chain_freshA vsubstA_commute_diff) . .
            subgoal apply(cases "x = z2", simp_all)
              subgoal apply(cases "y = z1", simp_all)
                subgoal by (smt (z3) uu uu' vsubstA_chain vsubstA_chain_freshA vsubstA_commute_diff)
                subgoal apply(cases "y = z2", simp_all)
                  subgoal by (smt (z3) uu uu' vsubstA_chain vsubstA_chain_freshA vsubstA_commute_diff)
                  subgoal by (smt (z3) uu uu' vsubstA_chain vsubstA_chain_freshA vsubstA_commute_diff) . .
              subgoal apply(cases "y = z1", simp_all)
                subgoal by (smt (z3) freshA_vsubstA2 uu uu' vsubstA_chain_freshA vsubstA_commute_diff)
                subgoal apply(cases "y = z2", simp_all)
                  subgoal by (smt (z3) uu uu' vsubstA_chain vsubstA_chain_freshA vsubstA_commute_diff)
                  subgoal 
                    by (smt (z3) freshA_vsubstA2 swapA_any uu uu' vsubstA_commute_diff) . . . . . . . .
qed


(* *)

lemma freshA_swapA_vsubstA: 
  assumes "freshA y a" 
  shows "swapA a y x = vsubstA a y x"
proof-
  have "finite ({uu. \<not> freshA uu a} \<union> {x,y})"  
  	by (simp add: cofinite_freshA)
  then obtain uu where uu: "uu \<noteq> x \<and> uu \<noteq> y \<and> freshA uu a" 
    by (metis (no_types, lifting) UnCI exists_var insertCI mem_Collect_eq)
  show ?thesis apply(subst swapA_any[of uu])
    subgoal using uu by simp
    subgoal using assms freshA_vsubstA2 freshA_vsubstA_idle uu by force .
qed 

end (* context Renset_FinSupp *)

sublocale Renset_FinSupp < Sw: Pre_Nominal_Set where swapA = swapA
  using Pre_Nominal_Set_def swapA_cmp swapA_id swapA_invol by blast

context Renset_FinSupp 
begin

(* Freshness is the same as the one in the just define swappable set: *)
lemma freshA_swapA: "freshA x a \<longleftrightarrow> Sw.freshA x a"
proof-
  have 0: "{y. swapA a y x \<noteq> a} \<subseteq> {y. vsubstA a y x \<noteq> a} \<union> {y. \<not> freshA y a}"
    using freshA_swapA_vsubstA by auto
  have 
    1: "{y. vsubstA a y x \<noteq> a} \<subseteq> {y. swapA a y x \<noteq> a} \<union> {y. \<not> freshA y a}"
    using freshA_swapA_vsubstA by auto
  show ?thesis unfolding freshA_def using cofinite_freshA  
    unfolding Sw.freshA_def by (metis 0 1 finite_Un rev_finite_subset)
qed

end (* context Renset_FinSupp *)


text \<open>The statement that any finitely supported renset produces a nominal set 
is written as sublocale inclusions. \<close>


text \<open>... the object component: \<close>
sublocale Renset_FinSupp < Sw: Nominal_Set where swapA = swapA
  apply standard unfolding freshA_swapA[symmetric] 
	by (simp add: cofinite_freshA)

text \<open>... the morphism component: \<close>
sublocale Renset_Morphism < F: Nominal_Morphism where 
  swapA = A.swapA and swapB = B.swapA and f = f
  apply standard
  by (metis (no_types, opaque_lifting) A.Renset_axioms A.swapA 
      B.Renset_FinSupp_axioms B.Renset_axioms 
      Renset.freshA_iff_ex_vvsubstA_idle 
      Renset_FinSupp.swapA_any f_substA_substB insertCI)



end 