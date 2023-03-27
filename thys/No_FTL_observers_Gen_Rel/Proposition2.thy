(*
   Author: Mike Stannett
   Date: August 2020
   Updated: Feb 2023
*)

section \<open> Proposition2 \<close>

text \<open>This theory shows that affine approximations map surfaces of cones
to (subsets of) surfaces of cones.\<close>

theory Proposition2
  imports  TangentLineLemma
begin


class Proposition2 = TangentLineLemma
begin

lemma lemProposition2:
  assumes "affineApprox A (wvtFunc m k) x"
  shows   "applyToSet (asFunc A) (coneSet m x) \<subseteq> coneSet k (A x)"
proof -

  define y where y: "y = A x"
  define lhs where lhs: "lhs = applyToSet (asFunc A) (coneSet m x)"
  define rhs where rhs: "rhs = coneSet k y"

  have mkxy: "wvtFunc m k x y" 
    using assms lemAffineEqualAtBase[of "wvtFunc m k" "A" "x"] y
    by auto
  have affA: "affine A" using assms by auto


  { fix q
    { assume q: "q \<in> lhs"
      hence "\<exists> p . (p \<in> coneSet m x) \<and> (asFunc A) p q" using lhs by auto
      then obtain p where
        p: "(p \<in> coneSet m x) \<and> (asFunc A) p q" 
        by presburger
  
      hence qAp: "q = A p" using affA by auto
  
      have  "cone m x p" using p by auto
      then obtain l where
        l: "(onLine p l) \<and>  (onLine x l) \<and> (\<exists> ph . Ph ph \<and> tl l m ph x)"
        by auto
      then obtain ph where ph: "Ph ph \<and> tl l m ph x" by auto
      have lineL: "isLine l" using l by auto
      have tll: "tl l m ph x" using ph by auto
  
      define l' where l': "l' = applyToSet (asFunc A) l"
      hence aatl: "applyAffineToLine A l l'"
        using lineL affA lemAffineOfLineIsLine[of "l" "A" "l'"]
        by simp
  
      hence tll': "tl l' k ph y"
        using assms(1) tll mkxy 
              lemTangentLines[of "m" "k" "A" "x" "ph" "l" "l'" "y"]
        by simp
  
      hence "(Ph ph \<and> tl l' k ph y)" 
        using ph by auto
      hence exPh: "\<exists> ph . (Ph ph \<and> tl l' k ph y)" 
        using exI[of "\<lambda> b. (Ph b \<and> tl l' k b y)" "ph"]
        by auto
  
      have "p \<in> l" using l by auto
      hence "q \<in> l'" using qAp q l' by auto
      moreover have lineL': "isLine l'" using tll' by auto
      ultimately have qonl': "onLine q l'" by auto
  
      hence "(onLine q l') \<and>  (onLine y l') \<and> (\<exists> ph . Ph ph \<and> tl l' k ph y)"
        using exPh tll' by blast
  
      hence "q \<in> rhs" using y tll' rhs by auto
    }
    hence "q \<in> lhs \<longrightarrow> q \<in> rhs" by auto
  }
  hence l2r: "lhs \<subseteq> rhs" by auto
  thus ?thesis using lhs rhs y by auto
qed




end (* of class Proposition2 *)

end (* of theory Proposition2 *)

