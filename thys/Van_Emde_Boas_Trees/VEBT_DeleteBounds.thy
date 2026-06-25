(*by Ammer*)
theory VEBT_DeleteBounds imports VEBT_Bounds VEBT_Delete  VEBT_DeleteCorrectness
begin

subsection \<open>Running Time Bounds for Deletion\<close>

context begin
interpretation VEBT_internal .

fun T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) 0 = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) (Suc 0) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) (Suc (Suc n)) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node None deg treeList summary) _ = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) 0 treeList summary) x = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) (Suc 0) treeList summary) x =1 "|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3 + ( 
              if (x < mi \<or> x > ma) then 1 
              else 3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )))"

end

context VEBT_internal begin                       
                       
lemma tdeletemimi:
  assumes "deg \<ge> 2"
  shows "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, mi)) deg treeList summary) x \<le> 9"
proof -
  obtain deg' :: nat where "deg = Suc (Suc deg')"
    using add_2_eq_Suc assms le_Suc_ex by blast

  then show ?thesis
    by simp
qed


lemma minNull_delete_time_bound: "invar_vebt t n \<Longrightarrow> minNull (vebt_delete t x) \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e t x \<le> 9" 
proof(induction  t n rule: invar_vebt.induct)
  case (1 a b)
  then consider "x = 0" | "x = Suc 0" | x' where "x = Suc (Suc x')"
    by (metis nat.exhaust)
  then show ?case
    by cases simp_all
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  show ?case
  proof (cases "mi = ma")
    case True
    then show ?thesis
      using \<open>2 \<le> deg\<close> tdeletemimi by metis
  next
    case False
    obtain mi' ma' treeList' summary' where
      "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
          Node (Some (mi', ma')) deg treeList' summary'" (is "?LHS = ?RHS mi' ma' treeList' summary'")
    proof atomize_elim
      show "\<exists>mi' ma' treeList' summary'. ?LHS = ?RHS mi' ma' treeList' summary'"
      proof (cases "x < mi \<or> x > ma")
        case True
        show ?thesis
          by (simp add: delt_out_of_range[OF True \<open>2 \<le> deg\<close>])
      next
        case False
        then have "mi \<le> x \<and> x \<le> ma"
          by linarith
        then show ?thesis
          by (simp
              add: del_in_range[of mi x ma deg, OF \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>mi \<noteq> ma\<close> \<open>2 \<le> deg\<close>] Let_def
              split: if_split)
      qed
    qed
    then have "\<not> minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)"
      by simp
    then have False
      using \<open>minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)\<close>
      by contradiction
    then show ?thesis ..
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  show ?case
  proof (cases "mi = ma")
    case True
    then show ?thesis
      using \<open>2 \<le> deg\<close> tdeletemimi by metis
  next
    case False
    obtain mi' ma' treeList' summary' where
      "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
          Node (Some (mi', ma')) deg treeList' summary'" (is "?LHS = ?RHS mi' ma' treeList' summary'")
    proof atomize_elim
      show "\<exists>mi' ma' treeList' summary'. ?LHS = ?RHS mi' ma' treeList' summary'"
      proof (cases "x < mi \<or> x > ma")
        case True
        show ?thesis
          by (simp add: delt_out_of_range[OF True \<open>2 \<le> deg\<close>])
      next
        case False
        then have "mi \<le> x \<and> x \<le> ma"
          by linarith
        then show ?thesis
          by (simp
              add: del_in_range[of mi x ma deg, OF \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>mi \<noteq> ma\<close> \<open>2 \<le> deg\<close>] Let_def
              split: if_split)
      qed
    qed
    then have "\<not> minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)"
      by simp
    then have False
      using \<open>minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)\<close>
      by contradiction
    then show ?thesis ..
  qed
qed 

lemma delete_bound_height: "invar_vebt t n \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e t x \<le> (1+ height t)*70"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then consider "x = 0" | "x = Suc 0" | x' where "x = Suc (Suc x')"
    by (metis nat.exhaust)
  then show ?case
    by cases simp_all
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case by simp
next
  case (4 treeList n summary m deg mi ma)
  hence deggy: "deg \<ge> 2" 
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then obtain deg' :: nat where "deg = Suc (Suc deg')"
    using add_2_eq_Suc le_Suc_ex by blast
  then show ?case
  proof(cases " (x < mi \<or> x > ma)")
    case True
    hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 4"
      by (simp add: \<open>deg = Suc (Suc deg')\<close>)
    then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] by auto
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence 0: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  ))"
      by (simp add: \<open>deg = Suc (Suc deg')\<close>)    
    then show ?thesis 
    proof(cases " (x = mi \<and> x = ma)")
      case True
      hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 9" using 0 by simp
      then show ?thesis by simp
    next
      case False
      hence 1: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+
                (if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                 (if x = mi then 1 else 1)  +
                  (let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 0 
        by (simp add: False) 
      then show ?thesis 
      proof(cases "x = mi")
        case True
        let ?xn = " the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                   (let  l = low ?xn (deg div 2);
                   h = high ?xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1
          unfolding True Let_def
          by simp
        let ?l = "low ?xn (deg div 2)"
        let ?h = "high ?xn (deg div 2)"
        have 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                    (if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          using  2  by meson
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "4.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          have 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 37 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                              if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       ))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by simp
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1)        
                       ))"
            unfolding Let_def by linarith
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]   by presburger
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"] 
              using \<open>invar_vebt (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) n\<close> by blast       
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" by simp
            then show ?thesis 
            proof(cases "?xn =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" using 10 
                by presburger
              also have "\<dots> \<le> 55 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" using maxt_bound[of ?sn] by force
              also have "\<dots> \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 1 + 8 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))"
                by (cases " vebt_maxt ?sn"; fastforce)
              also have "\<dots> \<le> 67 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h"
                using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
              also have "\<dots> \<le> 67 + (1 + height summary) * 70"
                using "4.IH"(2) by simp
              also have "\<dots> \<le> 67 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h"
                using 10 by simp
              also have "\<dots> \<le> 52 +  (1+ height summary)*70"
                using "4.IH"(2) by simp
              also have "\<dots> \<le> 52 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n" 
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) (low (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   43 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "?xn = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            also have "\<dots> \<le> 55 + (1 + height (treeList ! ?h)) * 70"
              using "4.IH"(1) True by simp
            also have "\<dots> \<le> 55 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary]
              by (meson True mult_le_mono1 nat_add_left_cancel_le nth_mem)
            finally show ?thesis
              by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 34" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      next
        case False
        let ?l = "low x (deg div 2)"
        let ?h = "high x (deg div 2)"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+1 +1 +
                   (let  l = low x (deg div 2);
                   h = high x (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1  False by simp
        hence 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+(
                    if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          by (simp add: Let_def)
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "4.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          hence 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+ 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  
                      + 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                             if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by (smt (verit) True add.assoc)
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + 
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" by force
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]  by force
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"]
              using \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> by blast
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "x =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using 10 by presburger
              also have "\<dots> \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by force
              also have "\<dots> \<le> 45 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 1 + 8 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))"
                by (cases " vebt_maxt ?sn"; fastforce)
              also have "\<dots> \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
              also have "\<dots> \<le> 57 + (1+ height summary) * 70"
                using "4.IH"(2) by simp
              also have "\<dots> \<le> 57 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  (1+ height summary)*70"
                by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                42 +  (height (Node (Some (mi, ma)) deg treeList summary) )*70" using height_compose_summary[of summary "Some (mi, ma)" deg treeList ] 
                by (meson add_mono_thms_linordered_semiring(2) le_refl mult_le_mono order_trans)
              then show ?thesis by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n"
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high x (deg div 2)) (low x (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "x = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                           38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            also have "\<dots> \<le> 38 + (1 + height (treeList ! ?h)) * 70" 
              using "4.IH"(1) True by simp
            also have  "\<dots> \<le> 38 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary]
              by (meson True add_le_cancel_left mult_le_mono1 nth_mem)
            finally show ?thesis
              by presburger
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 22" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence deggy: "deg \<ge> 2" 
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then obtain deg' where "deg = Suc (Suc deg')"
    using add_2_eq_Suc le_Suc_ex by blast
  then show ?case
  proof(cases " (x < mi \<or> x > ma)")
    case True
    hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 4"
      by (simp add: \<open>deg = Suc (Suc deg')\<close>)
    then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] by auto
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence 0: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  ))"
      by (simp add: \<open>deg = Suc (Suc deg')\<close>)    
    then show ?thesis 
    proof(cases " (x = mi \<and> x = ma)")
      case True
      hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 9" using 0 by simp
      then show ?thesis by simp
    next
      case False
      hence 1: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+
                ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 0 
        by (simp add: False) 
      then show ?thesis 
      proof(cases "x = mi")
        case True
        let ?xn = " the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                   (let  l = low ?xn (deg div 2);
                   h = high ?xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1
          unfolding True Let_def
          by force
        let ?l = "low ?xn (deg div 2)"
        let ?h = "high ?xn (deg div 2)"
        have 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                    (if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          using  2  by meson
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "5.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          have 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 37 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                              if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       ))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by simp
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1)        
                       ))"
            unfolding Let_def
            by linarith
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]   by presburger
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"] 
              using \<open>invar_vebt (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) n\<close> by blast       
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)"
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "?xn =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using 10 by presburger
              also have 11: "\<dots> \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by force
              also have 12: "\<dots> \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 1 + 8 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))"
                by (cases " vebt_maxt ?sn"; fastforce)
              also have "\<dots> \<le> 67 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
              also have "\<dots> \<le> 67 + (1 + height summary) * 70"
                using "5.IH"(2) by simp
              also have "\<dots> \<le> 67 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              also have "\<dots> \<le> 52 +  (1+ height summary) * 70"
                using "5.IH"(2) by simp
              also have "\<dots> \<le> 52 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n" 
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) (low (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   43 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "?xn = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            also have "\<dots> \<le> 55 + (1 + height (treeList ! ?h)) * 70"
              using "5.IH"(1) True by simp
            also have "\<dots> \<le> 55 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70"
              using height_compose_child[of "treeList ! ?h" treeList "Some (mi, ma)" deg summary]
              by (meson True mult_le_mono1 nat_add_left_cancel_le nth_mem)
            finally show ?thesis
              by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +1" using 3 by simp
          also have "\<dots> \<le> 34"
            using mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"]
            by linarith
          finally show ?thesis
            by simp
        qed
      next
        case False
        let ?l = "low x (deg div 2)"
        let ?h = "high x (deg div 2)"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+1 +1 +
                   (let  l = low x (deg div 2);
                   h = high x (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 1  False by simp
        hence 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+(
                    if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )"
          by (simp add: Let_def)
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "5.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          hence 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+ 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  
                      + 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                             if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] 
            mint_bound[of "summary"] by (smt (verit) True add.assoc)
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + 
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" by force
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              using 5 minNull_bound[of ?newnode]  by force
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"]
              using \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> by blast
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "x =  ma")
              case True
              hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))"
                using 10 by presburger
              also have "\<dots> \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by linarith
              also have "\<dots> \<le> 45 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 1 + 8 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))"
                by (cases " vebt_maxt ?sn"; fastforce)
              also have "\<dots> \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h"
                using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
              also have "\<dots> \<le> 57 +  (1+ height summary)*70"
                using "5.IH"(2) by simp
              also have "\<dots> \<le> 57 +  (height  (Node (Some (mi, ma)) deg treeList summary) )*70"
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis by presburger
            next
              case False
              hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h" 
                using 10 by simp
              also have "\<dots> \<le> 42 + (1 + height summary) * 70"
                using "5.IH"(2) by simp
              also have "\<dots> \<le> 42 + (height (Node (Some (mi, ma)) deg treeList summary)) * 70" 
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by simp
              finally show ?thesis
                by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n"
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high x (deg div 2)) (low x (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "x = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                                 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            also have "\<dots> \<le> 38 + (1 + height (treeList ! ?h))*70" 
              by (meson "5.IH"(1) True le_trans nat_add_left_cancel_le nth_mem)
            also have "\<dots> \<le> 38 + (height  (Node (Some (mi, ma)) deg treeList summary))*70"
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary]
              by (meson True mult_le_mono1 nat_add_left_cancel_le nth_mem)
            finally show ?thesis
              by presburger
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 22" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

theorem delete_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e  t x \<le> 140 + 70 * lb (lb u)"
  using delete_bound_height[of t n x] height_double_log_univ_size[of u n t] by simp

fun T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) 0 = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) (Suc 0) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) (Suc (Suc n)) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node None deg treeList summary) _ = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) 0 treeList summary) x = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) (Suc 0) treeList summary) x =1 "|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x =  ( 
              if (x < mi \<or> x > ma) then 1 
              else if (x = mi \<and> x = ma) then 1
              else  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary h        
                             else 1      
                       ))else  1  ))"


lemma tdeletemimi':"deg \<ge> 2 \<Longrightarrow> T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, mi)) deg treeList summary) x \<le> 1"
  using T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi mi "deg-2" treeList summary x]
  apply(cases "x \<noteq> mi") 
  apply (metis add_2_eq_Suc' le_add_diff_inverse2 le_eq_less_or_eq linorder_neqE_nat) 
  by (metis add_2_eq_Suc' eq_imp_le le_add_diff_inverse2)

lemma minNull_delete_time_bound': "invar_vebt t n \<Longrightarrow> minNull (vebt_delete t x) \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' t x \<le> 1" 
proof(induction t n rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    by (metis T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(1) T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(2) T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3) vebt_buildup.cases order_refl)
next
  case (4 treeList n summary m deg mi ma)
  then obtain n' :: nat where "n = Suc n'"
    by (metis One_nat_def VEBT_internal.set_n_deg_not_0 gr0_implies_Suc linorder_not_less not_less_eq_eq)
  then have "deg = Suc (Suc (n' + n'))"
    unfolding \<open>deg = n + m\<close> \<open>m = n\<close> by linarith
  show ?case 
  proof (cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "4.prems" \<open>deg = Suc (Suc _)\<close> delt_out_of_range by force
  next
    case False
    hence "x \<le> ma \<and> x \<ge> mi" by simp
    show ?thesis
    proof (cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>deg = Suc (Suc _)\<close> tdeletemimi' by force
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then obtain mi' ma' treeList' summary' where
        "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
            Node (Some (mi', ma')) deg treeList' summary'"
        by atomize_elim (simp add: \<open>deg = Suc (Suc _)\<close> Let_def)
      then have "\<not> minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)"
        by simp
      then have False
        using \<open>minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)\<close>
        by contradiction
      then show ?thesis ..
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  then obtain n' :: nat where "n = Suc n'"
    by (metis One_nat_def VEBT_internal.set_n_deg_not_0 gr0_implies_Suc linorder_not_less not_less_eq_eq)
  then have "deg = Suc (Suc (Suc (n' + n')))"
    unfolding \<open>deg = n + m\<close> \<open>m = Suc n\<close> by linarith
  show ?case 
  proof (cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "5.prems" \<open>deg = Suc (Suc _)\<close> delt_out_of_range by force
  next
    case False
    hence "mi \<le> x" and"x \<le> ma" by simp_all
    then show ?thesis
    proof (cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>deg = Suc (Suc _)\<close> tdeletemimi' by force
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then obtain mi' ma' treeList' summary' where
        "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
            Node (Some (mi', ma')) deg treeList' summary'"
        by atomize_elim (simp add: \<open>deg = Suc (Suc _)\<close> Let_def)
      then have "\<not> minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)"
        by simp
      then have False
        using \<open>minNull (vebt_delete (Node (Some (mi, ma)) deg treeList summary) x)\<close>
        by contradiction
      then show ?thesis ..
    qed
  qed
qed simp+


lemma delete_bound_height': "invar_vebt t n \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' t x \<le> 1+ height t"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    apply(cases "x \<le> 0")
    apply simp
    apply(cases "x = 1") 
    apply simp 
    using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3)[of a b "x-2"] height.simps(1)[of a b]
    by (metis One_nat_def T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3) vebt_buildup.cases lessI less_Suc_eq_le plus_1_eq_Suc)
next
  case (4 treeList n summary m deg mi ma)
  then obtain n' :: nat where "n = Suc n'"
    by (metis deg_not_0 gr0_implies_Suc)
  then have "deg = Suc (Suc (n' + n'))"
    using \<open>deg = n + m\<close> \<open>m = n\<close> by presburger
  show ?case 
  proof (cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis
      by (simp add: \<open>deg = Suc (Suc _)\<close>)
  next
    case False
    hence miama:"mi \<le> x \<and> x \<le> ma" by simp
    then show ?thesis
    proof(cases "x = mi \<and> x = ma")
      case True
      then show ?thesis
        by (simp add: \<open>deg = Suc (Suc _)\<close>)
    next
      case False  
      let ?xn = "(if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)"
      let ?minn = "(if x = mi then ?xn else mi)"
      let ?l = "low ?xn (deg div 2)"
      let ?h = "high ?xn (deg div 2)"
      have 0:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = (if ?h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1      
                       ))else  1)"
        using False miama
        by (simp add: \<open>deg = Suc (Suc _)\<close> Let_def)
      show ?thesis
      proof (cases "?h < length treeList")
        case True
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]"
        have 1:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                               T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                             if minNull ?newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1  )" using 0 True by simp
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l \<le> 1" 
            by (metis "0" "1" "4.IH"(1) minNull_delete_time_bound' nat_le_iff_add nth_mem)
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h"
            using 1 True by auto
          also have "\<dots> \<le> 1+1+ height summary"
            using 4(2)[of ?h] by simp
          also have "\<dots> \<le> 1 + height (Node (Some (mi, ma)) deg treeList summary)"
            by simp
          finally show ?thesis .
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                              1+  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l   " using 1 by simp
          also have "\<dots> \<le> 1 + 1 + height (treeList ! ?h)"
            using "4.IH"(1) True by force
          also have "\<dots> \<le> 1 + height (Node (Some (mi, ma)) deg treeList summary)"
            by (simp add: True)
          finally show ?thesis .
        qed
      qed (simp add : 0)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  then obtain n' :: nat where "n = Suc n'"
    by (metis Suc_0_div_numeral(1) Suc_eq_plus1_left add.commute div_by_1 list_decode.cases nth_mem
        numerals(1) valid_0_not)
  then have "deg = Suc (Suc (Suc (n' + n')))"
    using \<open>deg = n + m\<close> \<open>m = Suc n\<close> by presburger
  show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis
      by (simp add: \<open>deg = Suc (Suc _)\<close>)
  next
    case False
    hence miama:"mi \<le> x \<and> x \<le> ma" by simp
    then show ?thesis
    proof(cases "x = mi \<and> x = ma")
      case True
      then show ?thesis
        by (simp add: \<open>deg = Suc (Suc _)\<close>)
    next
      case False  
      let ?xn = "(if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)"
      let ?minn = "(if x = mi then ?xn else mi)"
      let ?l = "low ?xn (deg div 2)"
      let ?h = "high ?xn (deg div 2)"
      have 0:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = (if ?h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1      
                       ))else  1)"
        using False miama
        by (simp add: \<open>deg = Suc (Suc _)\<close> Let_def)
      show ?thesis 
      proof (cases "?h < length treeList")
        case True
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]"
        have 1:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                               T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                             if minNull ?newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1  )" using 0 True by simp
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l \<le> 1" 
            by (metis "0" "1" "5.IH"(1) minNull_delete_time_bound' nat_le_iff_add nth_mem)
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1+ T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h"
            using 1 True by auto
          also have "\<dots> \<le> 1 + 1 + height summary"
            using 5(2)[of ?h] by simp
          also have "\<dots> \<le> 1 + height (Node (Some (mi, ma)) deg treeList summary)"
            by simp
          finally show ?thesis .
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                              1+  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l   " using 1 by simp
          also have "\<dots> \<le> 1 + 1+ height (treeList ! ?h)" 
            using "5.IH"(1) True by auto
          also have "\<dots> \<le> 1 + height (Node (Some (mi, ma)) deg treeList summary)"
            by (simp add: True)
          finally show ?thesis .
        qed
      qed (simp add : 0)
    qed
  qed
qed simp+

theorem delete_bound_size_univ': "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'  t x \<le> 2 +  lb (lb u)"
  using delete_bound_height'[of t n x] height_double_log_univ_size[of u n t] by simp

end
end
