(**       Algebra4  
                            author Hidetsune Kobayashi
                                   Lingjun Chen (part of Chap 4. section 2, 
                                   with revision by Hirokazu Murao)
                             Group You Santo
                             Department of Mathematics
                             Nihon University
                             hikoba@math.cst.nihon-u.ac.jp
                             May 3, 2004.

 chapter 3.  Group Theory. Focused on Jordan Hoelder theorem (continued)
   section 20. (continued)
     subsection 20-1. Homomorphism of abelian groups
     subsection 20-2  quotient abelian group
   section 21  direct product and direct sum of abelian groups, 
               in general case

 chapter 4.  Ring theory
   section 1.  Definition of a ring and an ideal
   section 2.  Calculation of elements
   section 3.  ring homomorphisms
   section 4.  quotient rings
   section 5.  primary ideals, prime ideals
   section 6.  operation of ideals
 **)

theory Algebra4 = Algebra3 + Zorn:

section "20. continued "

lemma pOp_cancel_l:"\<lbrakk> agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;  c +\<^sub>G a =  c +\<^sub>G b \<rbrakk> \<Longrightarrow> a = b"
apply (insert bothl_eq [of "b_ag G" "c" "a" "b"])
apply (frule b_ag_group) apply simp
apply (subgoal_tac "carrier (b_ag G) = carrier G") apply simp
apply (subgoal_tac "tOp (b_ag G) = pOp G") apply simp
apply (simp add:b_ag_def)+
done

lemma pOp_cancel_r:"\<lbrakk> agroup G; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G;  a +\<^sub>G c =  b +\<^sub>G c \<rbrakk> \<Longrightarrow> a = b"
apply (subgoal_tac "c +\<^sub>G a =  c +\<^sub>G b") apply (simp add:pOp_cancel_l)
apply (simp add:ag_pOp_commute)
done

lemma ag_eq_diffzero:"\<lbrakk>agroup G; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow>
         (a = b) = (a +\<^sub>G (-\<^sub>G b) = 0\<^sub>G)" 
apply (rule iffI)
 apply (simp add:ag_r_inv1)
 apply (frule ag_mOp_closed[of "G" "b"], assumption+)
 apply (frule ag_inc_zero[of "G"]) 
 apply (subst ag_eq_sol2[of "G" "-\<^sub>G b" "a" "0\<^sub>G"], assumption+)
 apply (simp add:ag_inv_inv) apply (simp add:ag_l_zero)
done

lemma asubg_nsubg:"\<lbrakk> agroup G; H <+ G \<rbrakk> \<Longrightarrow>  H \<lhd> (b_ag G)"
apply (rule nmlSubg2)
 apply (simp add:b_ag_group)
 apply (simp add:asubgroup_def)
apply (rule ballI)+
 apply (subgoal_tac "tOp (b_ag G) = pOp G")
 apply (subgoal_tac "iOp (b_ag G) = mOp G")  apply simp
 apply (subgoal_tac "a +\<^sub>G h = h +\<^sub>G a") apply simp
 apply (subst ag_pOp_assoc, assumption+) 
 apply (simp add:asubg_subset1)
 apply (simp add:b_ag_def)  apply (subgoal_tac "carrier (b_ag G) = carrier G")
 apply (simp add:ag_mOp_closed)  apply (simp add:b_ag_def)
 apply (subgoal_tac "carrier (b_ag G) = carrier G") apply simp
apply (simp add:ag_r_inv1)
 apply (rule asubg_pOp_closed, assumption+) 
 apply (simp add:asubg_inc_zero)  apply (simp add:b_ag_def)
apply (rule ag_pOp_commute, assumption+)  apply (simp add:b_ag_def)
 apply (simp add:asubg_subset1) apply (simp add:b_ag_def)+
done

lemma subg_asubg:"\<lbrakk>agroup G; H \<guillemotleft> b_ag G\<rbrakk> \<Longrightarrow> H <+ G"
apply (frule agop_gop ) apply (frule agiop_giop) apply (simp add:asubgroup_def)
done
 

lemma asubg_test:"\<lbrakk>agroup G; H \<subseteq> carrier G; H \<noteq> {}; 
               \<forall>a\<in>H. \<forall>b\<in>H. a +\<^sub>G (-\<^sub>G b) \<in> H\<rbrakk> \<Longrightarrow> H <+ G"
apply (simp add:asubgroup_def) apply (frule b_ag_group [of "G"]) 
apply (simp add:ag_carrier_carrier [of "G", THEN sym])
apply (rule subg_condition [of "b_ag G" "H"], assumption+)
apply (rule allI)+ apply (rule impI)
apply (simp add:agop_gop agiop_giop)
done 

subsection "20-1. Homomorphism of abelian groups"

constdefs
  aHom::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme] \<Rightarrow> ('a \<Rightarrow> 'b) set"
  "aHom F G == {f. f \<in> carrier F \<rightarrow> carrier G \<and> f \<in> extensional (carrier F) \<and>
                  (\<forall>a\<in>carrier F. \<forall>b\<in>carrier F. f (a +\<^sub>F b) = (f a) +\<^sub>G (f b))}"

constdefs
 compos::"[('a, 'm) AgroupType_scheme, 'b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> 'a \<Rightarrow> 'c"
 "compos F g f == compose (carrier F) g f"

constdefs
 ker::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme] \<Rightarrow> ('a \<Rightarrow> 'b)
        \<Rightarrow> 'a set" ("(3ker\<^sub>_\<^sub>,\<^sub>_/ _)" [82,82,83]82)
 "ker\<^sub>F\<^sub>,\<^sub>G f == {a. a \<in> carrier F \<and> f a = (0\<^sub>G)}"

constdefs
 injec::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3injec\<^sub>_\<^sub>,\<^sub>_/ _)" [82,82,83]82)
 "injec\<^sub>F\<^sub>,\<^sub>G f == f \<in> aHom F G \<and> ker\<^sub>F\<^sub>,\<^sub>G f = {0\<^sub>F}"

constdefs
 surjec::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3surjec\<^sub>_\<^sub>,\<^sub>_/ _)" [82,82,83]82)
 "surjec\<^sub>F\<^sub>,\<^sub>G f == f \<in> aHom F G \<and> surj_to f (carrier F) (carrier G)"  

constdefs
 bijec::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> bool"             ("(3bijec\<^sub>_\<^sub>,\<^sub>_/ _)" [82,82,83]82)
 "bijec\<^sub>F\<^sub>,\<^sub>G f == injec\<^sub>F\<^sub>,\<^sub>G f \<and>surjec\<^sub>F\<^sub>,\<^sub>G f" 
 
lemma aHom_mem:"\<lbrakk>agroup F; agroup G; f \<in> aHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
                       f a \<in> carrier G"
apply (simp add:aHom_def) apply (erule conjE)+
apply (simp add:funcset_mem)
done

lemma aHom_add:"\<lbrakk>agroup F; agroup G; f \<in> aHom F G; a \<in> carrier F; 
 b \<in> carrier F\<rbrakk> \<Longrightarrow> f (a +\<^sub>F b) = (f a) +\<^sub>G (f b)" 
apply (simp add:aHom_def)
done

lemma aHom_0_0:"\<lbrakk>agroup F; agroup G; f \<in> aHom F G\<rbrakk> \<Longrightarrow> f (0\<^sub>F) = 0\<^sub>G"
apply (frule ag_inc_zero [of "F"])
apply (subst ag_l_zero [THEN sym, of "F" "0\<^sub>F"], assumption+)
apply (simp add:aHom_add)
apply (frule ag_l_zero [THEN sym, of "F" "0\<^sub>F"], assumption+)
apply (subgoal_tac "f (0\<^sub>F) = f (0\<^sub>F +\<^sub>F (0\<^sub>F))") prefer 2 apply simp
apply (thin_tac "0\<^sub>F =  0\<^sub>F +\<^sub>F 0\<^sub>F")
apply (simp add:aHom_add) apply (frule sym) 
apply (thin_tac "f (0\<^sub>F) =  f (0\<^sub>F) +\<^sub>G (f (0\<^sub>F))")
apply (simp add:aHom_def) apply (frule conj_1)
apply (frule funcset_mem, assumption+) 
apply (frule ag_eq_sol2[of "G" "f (0\<^sub>F)" "f (0\<^sub>F)"  "f (0\<^sub>F)"], assumption+ )
apply (simp add:ag_r_inv1)
done

lemma aHom_inv_inv:"\<lbrakk>agroup F; agroup G; f \<in> aHom F G; a \<in> carrier F\<rbrakk> \<Longrightarrow>
                         f (-\<^sub>F a) = -\<^sub>G (f a)"
apply (frule ag_inc_zero [of "F"])
apply (frule ag_l_inv1 [of "F" "a"], assumption+)
apply (subgoal_tac "f (-\<^sub>F a +\<^sub>F a) = f (0\<^sub>F)") prefer 2 apply simp
 apply (thin_tac "-\<^sub>F a +\<^sub>F a = 0\<^sub>F")
 apply (frule ag_mOp_closed [of "F" "a"], assumption+)
apply (simp add:aHom_add)
apply (simp add:aHom_0_0)
 apply (simp add:aHom_def) apply (frule conj_1)
 apply (frule funcset_mem [of "f" "carrier F" "carrier G" "a"], assumption+)
 apply (frule funcset_mem [of "f" "carrier F" "carrier G" "-\<^sub>F a"], assumption+)
apply (subst ag_eq_sol2 [of "G" "f a" "f (-\<^sub>F a)" "0\<^sub>G"], assumption+) 
 apply (simp add:ag_inc_zero) apply assumption
apply (rule ag_l_zero, assumption+)
apply (simp add:ag_mOp_closed)
done

lemma aHom_compos:"\<lbrakk>agroup L; agroup M; agroup N; f \<in> aHom L M; g \<in> aHom M N \<rbrakk>
  \<Longrightarrow> compos L g f \<in> aHom L N" 
apply (simp add:aHom_def [of "L" "N"])
apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:compos_def compose_def)
 apply (rule aHom_mem [of "M" "N" "g"], assumption+)
 apply (simp add:aHom_mem [of "L" "M" "f"])
apply (rule conjI)
 apply (simp add:compos_def compose_def extensional_def)
apply (rule ballI)+
 apply (simp add:compos_def compose_def)
 apply (simp add:ag_pOp_closed)
 apply (simp add:aHom_add)
 apply (rule aHom_add, assumption+)
 apply (simp add:aHom_mem)+
done

constdefs
 aimg ::"[('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme, 'a \<Rightarrow> 'b]
            \<Rightarrow> 'b AgroupType"  ("(3aimg\<^sub>_\<^sub>,\<^sub>_ _)" [82,82,83]82)
  "aimg\<^sub>F\<^sub>,\<^sub>G f == \<lparr> carrier = f ` (carrier F), pOp = pOp G, mOp = mOp G,
                  zero = zero G\<rparr>"

lemma ker_subg:"\<lbrakk>agroup F; agroup G; f \<in> aHom F G \<rbrakk> \<Longrightarrow> ker\<^sub>F\<^sub>,\<^sub>G f <+ F"
apply (rule asubg_test, assumption+)
apply (rule subsetI)
 apply (simp add:ker_def)
apply (simp add:ker_def)
apply (frule aHom_0_0 [of "F" "G" "f"], assumption+)
apply (frule ag_inc_zero [of "F"]) apply blast
apply (rule ballI)+
apply (simp add:ker_def) apply (erule conjE)+
apply (rule conjI)
apply (rule ag_pOp_closed, assumption+)
apply (rule ag_mOp_closed, assumption+) 
apply (frule_tac x = b in ag_mOp_closed [of "F"], assumption+)
apply (simp add:aHom_add)
apply (simp add:aHom_inv_inv)
apply (frule ag_inc_zero [of "G"])
apply (subst ag_r_inv1, assumption+)
apply simp
done

subsection "20-2 quotient abelian group"

constdefs
 ar_coset :: "['a, ('a, 'more)  AgroupType_scheme, 'a set] \<Rightarrow> 'a set"
     ("(3_ \<uplus>\<^sub>_ _)" [66,66,67]66)
  "ar_coset a R H == r_coset (b_ag R) H a"

 set_ar_cos:: "[('a, 'more) AgroupType_scheme, 'a set] \<Rightarrow> 'a set set"
  "set_ar_cos R I == {X. \<exists>a\<in>carrier R. X = ar_coset a R I}"

constdefs
 asettOp :: "[('a, 'more) AgroupType_scheme, 'a set, 'a set] \<Rightarrow> 'a set "
  "asettOp G H K == settOp (b_ag G) H K"

syntax 
  "@ASBOP1" :: "['a set, ('a, 'more) AgroupType_scheme, 'a set] \<Rightarrow> 'a set"
            ("(3_/ \<^bold>+\<^sub>_/ _)" [60,60,61]60)  
translations
  "H \<^bold>+\<^sub>G K" == "asettOp G H K"

lemma ag_a_in_ar_cos:"\<lbrakk>agroup G; H <+ G; a \<in> carrier G\<rbrakk> \<Longrightarrow> a \<in> a \<uplus>\<^sub>G H"
apply (simp add:ar_coset_def)
apply (simp add:ag_carrier_carrier[THEN sym])
apply (frule b_ag_group [of "G"]) apply (simp add:asubgroup_def)
apply (rule aInR_cos, assumption+)
done

lemma r_cos_subset:"\<lbrakk>agroup G; H <+ G; X \<in> set_r_cos (b_ag G) H\<rbrakk> \<Longrightarrow>
 X \<subseteq> carrier G" 
apply (simp add:set_r_cos_def r_coset_def) 
apply (subgoal_tac "\<forall>a \<in> carrier (b_ag G). {b. \<exists>h\<in>H.  h \<cdot>\<^sub>(b_ag G) a = b} \<subseteq>
  carrier G") 
apply blast
apply (rule ballI) apply (rule subsetI)
 apply (simp add:CollectI)
apply (subgoal_tac "\<forall>h\<in>H. h \<cdot>\<^sub>(b_ag G) a \<in> carrier G") apply blast
apply (rule ballI) 
apply (subgoal_tac "H \<subseteq> carrier G")   
apply (frule subsetD [of "H" "carrier G" _]) apply simp 
apply (subgoal_tac "tOp (b_ag G) = pOp G") apply simp 
apply (rule ag_pOp_closed) apply assumption+ apply (simp add:b_ag_def)
 apply (simp add:b_ag_def) apply (simp add:asubg_subset)
done

lemma asubg_costOp_commute:"\<lbrakk>agroup G; H <+ G; x \<in> set_r_cos (b_ag G) H;
 y \<in> set_r_cos (b_ag G) H\<rbrakk> \<Longrightarrow> costOp (b_ag G) H x y = costOp (b_ag G) H y x"
apply (simp add:set_r_cos_def)
apply (subgoal_tac "\<forall>a\<in>carrier (b_ag G). \<forall>b\<in>carrier (b_ag G). 
 x = H\<^sub>(b_ag G) a \<and> y = H\<^sub>(b_ag G) b \<longrightarrow> costOp (b_ag G) H x y = costOp (b_ag G) H y x") 
apply blast apply (thin_tac "\<exists>a\<in>carrier (b_ag G). x = H\<^sub>(b_ag G) a")
 apply (thin_tac "\<exists>a\<in>carrier (b_ag G). y = H\<^sub>(b_ag G) a")
apply (rule ballI)+ apply (rule impI)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x = H\<^sub>(b_ag G) a \<and> y = H\<^sub>(b_ag G) b")
 apply simp
apply (subst costOpwelldef [THEN sym])
 apply (simp add:b_ag_group)
 apply (simp add:asubg_nsubg)
 apply assumption+
apply (subst costOpwelldef [THEN sym])
 apply (simp add:b_ag_group)
 apply (simp add:asubg_nsubg)
 apply assumption+
apply (subgoal_tac "tOp (b_ag G) = pOp G")
 apply simp
 apply (subgoal_tac "a +\<^sub>G b =  b +\<^sub>G a") apply simp
 apply (rule ag_pOp_commute, assumption+)
apply (simp add:b_ag_def)+
done

lemma Subg_Qgroup:"\<lbrakk> agroup G; H <+ G \<rbrakk> \<Longrightarrow> agroup (aqgrp G H)" 
apply (simp add:agroup_def [of "aqgrp G H"])
apply (simp add:aqgrp_def)
apply (frule asubg_nsubg, assumption+)
apply (frule b_ag_group)
 apply (simp add:Qgrp_bOp [of "b_ag G" "H"])
 apply (simp add:Qgrp_iOp [of "b_ag G" "H"])
apply (simp add:ex_Qgrp_one [of "b_ag G" "H"]) 
apply (rule ballI)+
apply (simp add:asubg_costOp_commute) 
apply (simp add:qgrpInvTr [of "b_ag G" "H"])
apply (simp add:qgrpAssBopTr)
apply (simp add:qgrpUnitTr [of "b_ag G" "H"])
done

lemma plus_subgs:"\<lbrakk> agroup G; H1 <+ G; H2 <+ G \<rbrakk> \<Longrightarrow> H1 \<^bold>+\<^sub>G H2 <+ G"
apply (simp add:asettOp_def)
apply (subgoal_tac "nsubgroup (b_ag G) H2")
apply (simp add:asubgroup_def)
apply (subgoal_tac "group (b_ag G)")
apply (simp add:subgns [of "b_ag G" "H1" "H2"])
apply (rule b_ag_group) apply assumption
apply (simp add:asubg_nsubg)
done

lemma aqgrp_carrier:"\<lbrakk>agroup G; H <+ G \<rbrakk> \<Longrightarrow>
                   set_r_cos (b_ag G) H = set_ar_cos G H"
apply (simp add:set_ar_cos_def)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:ar_coset_def set_r_cos_def)
done

lemma aqgrp_pOp_maps:"\<lbrakk>agroup G; H <+ G; a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> 
      pOp (aqgrp G H) (a \<uplus>\<^sub>G H) (b \<uplus>\<^sub>G H) = (a +\<^sub>G b) \<uplus>\<^sub>G H"
apply (simp add:aqgrp_def ar_coset_def)
apply (frule b_ag_group)
apply (frule asubg_nsubg, assumption+)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (subst costOpwelldef [THEN sym], assumption+)
apply (simp add:agop_gop)
done
                           
lemma aqgrp_mOp_maps:"\<lbrakk>agroup G; H <+ G; a \<in> carrier G\<rbrakk> \<Longrightarrow> 
      mOp (aqgrp G H) (a \<uplus>\<^sub>G H) = (-\<^sub>G a) \<uplus>\<^sub>G H"
apply (simp add:aqgrp_def ar_coset_def)
apply (frule b_ag_group)
apply (frule asubg_nsubg, assumption+)
apply (simp add:ag_carrier_carrier [THEN sym])
apply (subst cosiOpwelldef, assumption+)
apply (simp add:agiop_giop)
done

lemma aqgrp_zero:"\<lbrakk>agroup G; H <+ G\<rbrakk> \<Longrightarrow> zero (aqgrp G H) = H"
apply (simp add:aqgrp_def)
done

constdefs
 rind_hom :: "[('a, 'more) AgroupType_scheme, ('b, 'more1) AgroupType_scheme, 
                ('a  \<Rightarrow> 'b)] \<Rightarrow> ('a set  \<Rightarrow> 'b )"
   "rind_hom A B f == \<lambda>X\<in>(set_ar_cos A (ker\<^sub>A\<^sub>,\<^sub>B f)). f ( \<some> x. x \<in> X)"

syntax 
 "@RIND_HOM"::"['a \<Rightarrow> 'b, ('a, 'm) AgroupType_scheme, ('b, 'm1) AgroupType_scheme]
 \<Rightarrow>  ('a set  \<Rightarrow> 'b )" ("(3_\<degree>\<^sub>_\<^sub>,\<^sub>_)" [82,82,83]82)  

translations
    "f\<degree>\<^sub>F\<^sub>,\<^sub>G " == "rind_hom F G f"


section "21 direct product and direct sum of abelian groups, in general case"

constdefs
 Un_carrier::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 'a set"
   "Un_carrier I A ==  \<Union>{X. \<exists>i\<in>I. X = carrier (A i)}"

 carr_prodag::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 
               ('i  \<Rightarrow> 'a ) set"  
 "carr_prodag I A == {f. f \<in> extensional I \<and> f \<in> I \<rightarrow> (Un_carrier I A) \<and> (\<forall>i\<in>I. f i \<in> carrier (A i))}"

 prod_pOp::"['i set,  'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 
    ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)"
  "prod_pOp I A  == \<lambda>f\<in>carr_prodag I A. \<lambda>g\<in>carr_prodag I A.
                           \<lambda>x\<in>I. (f x) +\<^sub>(A x) (g x)" 

 prod_mOp::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow>
                                  ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)"
  "prod_mOp I A  == \<lambda>f\<in>carr_prodag I A. \<lambda>x\<in>I. -\<^sub>(A x) (f x)" 

 prod_zero::"['i set,  'i  \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a)"
  "prod_zero I A == \<lambda>x\<in>I. 0\<^sub>(A x)"

 prodag::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) AgroupType" 
     
 "prodag I A == \<lparr> carrier = carr_prodag I A, 
   pOp = prod_pOp I A, mOp = prod_mOp I A,
   zero = prod_zero I A\<rparr>"  


 PRoject::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme, 'i]
                   \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a"
  "PRoject I A x == \<lambda>f\<in>carr_prodag I A. f x"

syntax 
  "@PRODag" :: "['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 
               ('i \<Rightarrow> 'a ) set"  ("(a\<Pi>\<^sub>_/ _)" [72,73]72)
translations
  "a\<Pi>\<^sub>I A" == "prodag I A"

lemma prod_pOp_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
    prod_pOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A \<rightarrow> carr_prodag I A"
apply (rule bivar_func_test)
apply (rule ballI)+
 apply (subst carr_prodag_def) apply (simp add:CollectI)
apply (rule conjI)
 apply (simp add:prod_pOp_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (subst Un_carrier_def) apply (simp add:CollectI)
 apply (subgoal_tac "agroup (A x)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. agroup (A k)")
 apply (simp add:carr_prodag_def) apply (erule conjE)+ 
 apply (thin_tac "a \<in> I \<rightarrow> Un_carrier I A") 
 apply (thin_tac "b \<in> I \<rightarrow> Un_carrier I A")
 apply (subgoal_tac "a x \<in> carrier (A x)") prefer 2 apply simp
 apply (subgoal_tac "b x \<in> carrier (A x)") prefer 2 apply simp
 apply (thin_tac "\<forall>i\<in>I. a i \<in> carrier (A i)")
 apply (thin_tac "\<forall>i\<in>I. b i \<in> carrier (A i)")
 apply (frule_tac x = "a x" and y = "b x" in ag_pOp_closed, assumption+)
 apply blast
apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (rule_tac G = "A i" and x = "a i" and y = "b i" in ag_pOp_closed)
 apply simp
 apply (simp add:carr_prodag_def)+
done
 
lemma prod_pOp_mem:"\<lbrakk>\<forall>k\<in>I. agroup (A k); X \<in> carr_prodag I A;
 Y \<in> carr_prodag I A\<rbrakk> \<Longrightarrow> prod_pOp I A X Y \<in> carr_prodag I A"
apply (subgoal_tac "prod_pOp I A X \<in> carr_prodag I A \<rightarrow> carr_prodag I A")
apply (simp add:funcset_mem)
apply (frule prod_pOp_func)
apply (simp add:funcset_mem)
done

lemma prod_mOp_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
                  prod_mOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A"
apply (rule univar_func_test)
apply (rule ballI)
 apply (simp add:prod_mOp_def)
 apply (simp add:carr_prodag_def) apply (erule conjE)+
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (rename_tac f j)
 apply (frule_tac f = f and x = j in funcset_mem [of _ "I" "Un_carrier I A"],
                             assumption+)
 apply (thin_tac "f \<in> I \<rightarrow> Un_carrier I A")
 apply (subgoal_tac "f j \<in> carrier (A j)") prefer 2 apply simp
 apply (thin_tac "f j \<in> Un_carrier I A")
 apply (subgoal_tac "agroup (A j)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. agroup (A k)") apply (thin_tac "\<forall>i\<in>I. f i \<in> carrier (A i)")
 apply (simp add:Un_carrier_def)
 apply (frule ag_mOp_closed, assumption+) 
 apply blast
apply (rule ballI) 
 apply (rule_tac G = "A i" and x = "x i" in ag_mOp_closed)
 apply simp+
done

lemma prod_mOp_mem:"\<lbrakk>\<forall>j\<in>I. agroup (A j); X \<in> carr_prodag I A\<rbrakk> \<Longrightarrow>
                         prod_mOp I A X \<in> carr_prodag I A"
apply (frule prod_mOp_func)
apply (simp add:funcset_mem)
done

lemma prod_zero_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
                           prod_zero I A \<in> carr_prodag I A"
apply (simp add:prod_zero_def prodag_def)
apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply simp
 apply (subgoal_tac "agroup (A x)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. agroup (A k)")
 apply (simp add:Un_carrier_def)
 apply (frule ag_inc_zero)
 apply auto
apply (subgoal_tac "agroup (A i)") prefer 2 apply simp
 apply (simp add:ag_inc_zero)
done

lemma carr_prodag_mem_eq:"\<lbrakk>\<forall>k\<in>I. agroup (A k); X \<in> carr_prodag I A;
Y \<in> carr_prodag I A; \<forall>l\<in>I. (X l) = (Y l) \<rbrakk> \<Longrightarrow> X = Y" 
apply (simp add:carr_prodag_def)
apply (erule conjE)+
apply (simp add:funcset_eq)
done

lemma prodag_agroup:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> agroup (prodag I A)" 
apply (simp add:agroup_def [of "(prodag I A)"])
apply (simp add:prodag_def)
 apply (simp add:prod_pOp_func)
 apply (simp add:prod_mOp_func)
 apply (simp add:prod_zero_func)
apply (rule ballI)+ 
apply (rule conjI)
 apply (frule prod_zero_func [of "I" "A"])
 apply (frule_tac X = "prod_zero I A" and Y = x in prod_pOp_mem [of "I" "A"], assumption+)
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (simp add:prod_zero_def)
 apply (rule ag_l_zero)
  apply simp
  apply (simp add: carr_prodag_def)
apply (rule conjI)
 apply (frule prod_mOp_func [of "I" "A"])
 apply (frule_tac x = x in funcset_mem [of "prod_mOp I A" "carr_prodag I A" _], assumption+)
 apply (frule_tac X = "prod_mOp I A x" and Y = x in prod_pOp_mem [of "I" "A"], assumption+)
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule prod_zero_func [of "I" "A"]) apply assumption
 apply (rule ballI)
 apply (simp add:prod_pOp_def prod_mOp_def prod_zero_def)
 apply (rule ag_l_inv1) apply simp
 apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (frule_tac X = x and Y = y in prod_pOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = y and Y = z in prod_pOp_mem [of "I" "A"], assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (rule prod_pOp_mem [of "I" "A"], assumption+)+
 apply (rule ballI)
 apply (simp add:prod_pOp_def)
apply (subgoal_tac "agroup (A l)") prefer 2 apply simp
 apply (rule ag_pOp_assoc, assumption+)
 apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def) 
apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule prod_pOp_mem, assumption+)
 apply (rule prod_pOp_mem, assumption+)
apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (rule ag_pOp_commute)
 apply simp apply (simp add:carr_prodag_def)+
done

lemma carrier_prodag:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
         carrier (prodag I A) = carr_prodag I A"
apply (simp add:prodag_def)
done

lemma prodag_elemfun:"\<lbrakk>\<forall>k\<in>I. agroup (A k); f \<in> carrier (prodag I A)\<rbrakk> \<Longrightarrow>
         f \<in> extensional I"
apply (simp add:carrier_prodag)
apply (simp add:carr_prodag_def)
done

lemma prodag_pOp:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  pOp (prodag I A) = prod_pOp I A"
apply (simp add:prodag_def)
done

lemma prodag_iOp:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  mOp (prodag I A) = prod_mOp I A"
apply (simp add:prodag_def)
done 

lemma prodag_zero:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  zero (prodag I A) = prod_zero I A"
apply (simp add:prodag_def)
done

lemma prodag_sameTr0:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> Un_carrier I A = Un_carrier I B"
apply (simp add:Un_carrier_def)
done

lemma prodag_sameTr1:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> carr_prodag I A = carr_prodag I B"
apply (simp add:carr_prodag_def)
apply (subgoal_tac "Un_carrier I A = Un_carrier I B") prefer 2
 apply (rule prodag_sameTr0 [of "I" "A" "B"]) 
 apply (rule ballI) apply (subgoal_tac "agroup (B k)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. agroup (B k)") apply (subgoal_tac "A k = B k")
 prefer 2 apply simp apply (thin_tac "\<forall>k\<in>I. A k = B k")
 apply (frule sym) apply (thin_tac "A k = B k") apply simp
 apply assumption
 apply simp 
done

lemma prodag_sameTr2:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_pOp I A = prod_pOp I B"
apply (frule prodag_sameTr1 [of "I" "A" "B"], assumption+)
apply (simp add:prod_pOp_def)
apply (rule bivar_func_eq)
apply (rule ballI)+
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_sameTr3:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_mOp I A = prod_mOp I B"
apply (frule prodag_sameTr1 [of "I" "A" "B"], assumption+)
apply (simp add:prod_mOp_def)
apply (rule funcset_eq [of _ "carr_prodag I B"])
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI)
apply (rename_tac g) apply simp
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_sameTr4:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_zero I A = prod_zero I B"
apply (simp add:prod_zero_def)
apply (rule funcset_eq [of _ "I"])
 apply (simp add:restrict_def extensional_def)+
done

lemma prodag_same:"\<lbrakk>\<forall>k\<in>I. agroup (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prodag I A = prodag I B"
apply (frule prodag_sameTr1, assumption+) 
apply (frule prodag_sameTr2, assumption+) 
apply (frule prodag_sameTr3, assumption+)
apply (frule prodag_sameTr4, assumption+)
apply (simp add:prodag_def)
done
      
lemma project_aHom:"\<lbrakk>\<forall>k\<in>I. agroup (A k); j \<in> I\<rbrakk> \<Longrightarrow>
                         PRoject I A j \<in> aHom (prodag I A) (A j)"
apply (simp add:aHom_def)
apply (rule conjI)
apply (rule univar_func_test)
 apply (rule ballI)
 apply (simp add:PRoject_def) apply (simp add:prodag_def)
 apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (simp add:PRoject_def restrict_def extensional_def)
 apply (rule allI) apply (rule impI) apply (simp add:prodag_def)
apply (rule ballI)+
 apply (simp add:prodag_def)
 apply (simp add:prod_pOp_def)
 apply (simp add:PRoject_def)
apply (subgoal_tac "(\<lambda>x\<in>I.  a x +\<^sub>(A x) (b x)) \<in>  carr_prodag I A")
 apply simp
 apply (simp add:carr_prodag_def) apply (erule conjE)+
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI) apply simp
 apply (subgoal_tac " a x +\<^sub>(A x) (b x) \<in> carrier (A x)")  
 apply (simp add:Un_carrier_def) apply blast
 apply (rule ag_pOp_closed) apply simp
 apply simp apply simp
apply (rule ballI)
 apply (rule ag_pOp_closed)
 apply simp+
done

 
constdefs
 A_to_prodag :: "[('a, 'm) AgroupType_scheme, 'i set, 'i \<Rightarrow>('a \<Rightarrow> 'b), 
 'i  \<Rightarrow> ('b, 'm1) AgroupType_scheme] \<Rightarrow> ('a \<Rightarrow> ('i \<Rightarrow>'b))"
 "A_to_prodag A I S B == \<lambda>a\<in>carrier A. \<lambda>k\<in>I. S k a" 
 (* I is an index set, A is an abelian group, S: I \<rightarrow> carrier A \<rightarrow> 
  carrier (prodag I B),   s i \<in> carrier A \<rightarrow> B i  *)  

lemma A_to_prodag_mem:"\<lbrakk>agroup A; \<forall>k\<in>I. agroup (B k);  \<forall>k\<in>I. (S k) \<in> 
 aHom A (B k); x \<in> carrier A \<rbrakk> \<Longrightarrow> A_to_prodag A I S B x \<in> carr_prodag I B"
apply (simp add:carr_prodag_def)
apply (rule conjI)
apply (simp add:A_to_prodag_def extensional_def restrict_def)
apply (simp add:Pi_def restrict_def A_to_prodag_def)
apply (rule conjI)  
apply (rule allI) apply (rule impI)
apply (simp add:Un_carrier_def) 
 apply (subgoal_tac "S xa \<in> aHom A (B xa)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (simp add:aHom_def) apply (erule conjE)+ 
 apply (frule_tac f = "S xa" and A = "carrier A" and B = "carrier (B xa)"
           and x = x in funcset_mem, assumption+)
 apply blast
apply (rule ballI)
 apply (subgoal_tac "S i \<in> aHom A (B i)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. S k \<in> aHom A (B k)")
 apply (simp add:aHom_def) apply (erule conjE)+
 apply (simp add:funcset_mem)
done
 
lemma A_to_prodag_aHom:"\<lbrakk>agroup A; \<forall>k\<in>I. agroup (B k); \<forall>k\<in>I. (S k) \<in> 
 aHom A (B k) \<rbrakk>  \<Longrightarrow> A_to_prodag A I S B \<in> aHom A (a\<Pi>\<^sub>I B)"
apply (simp add:aHom_def [of "A" "a\<Pi>\<^sub>I B"])
apply (rule conjI)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:prodag_def)
 apply (simp add: A_to_prodag_mem)
apply (rule conjI)
apply (simp add:A_to_prodag_def restrict_def extensional_def)
apply (rule ballI)+
 apply (frule_tac x = a and y = b in ag_pOp_closed, assumption+)
 apply (frule_tac x = "a +\<^sub>A b" in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule_tac x = a in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule_tac x = b in A_to_prodag_mem [of "A" "I" "B" "S"],
                                                       assumption+)
 apply (frule prodag_agroup [of "I" "B"])
 apply (subgoal_tac " A_to_prodag A I S B a \<in> carrier (a\<Pi>\<^sub>I B)")
 apply (subgoal_tac " A_to_prodag A I S B b \<in> carrier (a\<Pi>\<^sub>I B)")
 apply (frule_tac x = "A_to_prodag A I S B a" and 
 y = "A_to_prodag A I S B b" in ag_pOp_closed [of "a\<Pi>\<^sub>I B"], assumption+)
 apply (simp add:prodag_def)
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule ballI)
 apply (simp add:A_to_prodag_def prod_pOp_def)
 apply (subgoal_tac "S l \<in> aHom A (B l)")
 apply (simp add:aHom_add) apply simp
apply (simp add:prodag_def)+
done


constdefs
 finiteHom::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme, 'i \<Rightarrow> 'a] \<Rightarrow> bool"
  "finiteHom I A f == f \<in> carr_prodag I A \<and> (\<exists>H. H \<subseteq> I \<and> finite H \<and> (
    \<forall>j \<in> (I - H). (f j) = 0\<^sub>(A j)))" 

constdefs
 carr_dsumag::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 
               ('i  \<Rightarrow> 'a ) set"  
 "carr_dsumag I A == {f. finiteHom I A f}"

 dsumag::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) AgroupType" 
  "dsumag I A == \<lparr> carrier = carr_dsumag I A, 
   pOp = prod_pOp I A, mOp = prod_mOp I A,
   zero = prod_zero I A\<rparr>"  


 dProj::"['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme, 'i]
                   \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a"
  "dProj I A x == \<lambda>f\<in>carr_dsumag I A. f x"

syntax 
  "@DSUMag" :: "['i set, 'i \<Rightarrow> ('a, 'more) AgroupType_scheme] \<Rightarrow> 
               ('i \<Rightarrow> 'a ) set"  ("(a\<Oplus>~\<^sub>_/ _)" [72,73]72)
translations
  "a\<Oplus>~\<^sub>I A" == "dsumag I A"

lemma dsum_pOp_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
    prod_pOp I A \<in> carr_dsumag I A \<rightarrow> carr_dsumag I A \<rightarrow> carr_dsumag I A"
apply (rule bivar_func_test)
apply (rule ballI)+
 apply (subst carr_dsumag_def) apply (simp add:CollectI)
apply (simp add:finiteHom_def)
 apply (rule conjI)
 apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
 apply (erule conjE)+ apply (simp add:prod_pOp_mem)
apply (simp add:carr_dsumag_def finiteHom_def) apply (erule conjE)+
 apply (subgoal_tac "\<forall>H K. (H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. a j = 0\<^sub>(A j))) \<and>
    (K \<subseteq> I \<and> finite K \<and> (\<forall>j\<in>I - K. b j = 0\<^sub>(A j))) \<longrightarrow>
  (\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. prod_pOp I A a b j = 0\<^sub>(A j)))") 
 apply blast
 apply (thin_tac "\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. a j = 0\<^sub>A j)")
 apply (thin_tac "\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. b j = 0\<^sub>A j)")
 apply (rule allI)+ apply (rule impI) apply (erule conjE)
apply (subgoal_tac "H \<union> K \<subseteq> I \<and> finite (H \<union> K) \<and> (\<forall>j\<in>I - (H \<union> K).
           prod_pOp I A a b j = 0\<^sub>A j)")
 apply blast
 apply (rule conjI)
  apply (rule subsetI)  apply (erule conjE)+ apply simp
  apply (case_tac "x \<in> H") apply (simp add:subsetD) apply (simp add:subsetD)
 apply (rule conjI)
  apply (simp add:finite_UnI)
 apply (erule conjE)+
 apply (simp add:prod_pOp_def)
 apply (rule ballI) apply (subgoal_tac "j \<in> I") apply simp prefer 2
 apply simp
 apply (erule conjE)+
 apply (rule ag_l_zero) apply simp
 apply (rule ag_inc_zero) apply simp
done

lemma dsum_pOp_mem:"\<lbrakk>\<forall>k\<in>I. agroup (A k); X \<in> carr_dsumag I A;
 Y \<in> carr_dsumag I A\<rbrakk> \<Longrightarrow> prod_pOp I A X Y \<in> carr_dsumag I A"
apply (subgoal_tac "prod_pOp I A X \<in> carr_dsumag I A \<rightarrow> carr_dsumag I A")
apply (simp add:funcset_mem)
apply (frule dsum_pOp_func)
apply (simp add:funcset_mem)
done

lemma dsum_iOp_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
                  prod_mOp I A \<in> carr_dsumag I A \<rightarrow> carr_dsumag I A"
apply (rule univar_func_test)
apply (rule ballI)
 apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
 apply (erule conjE)+ apply (simp add:prod_mOp_mem)
apply (subgoal_tac "\<forall>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. x j = 0\<^sub>A j) \<longrightarrow>
  (\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. prod_mOp I A x j = 0\<^sub>(A j)))")
 apply blast
 apply (thin_tac "\<exists>H. H \<subseteq> I \<and> finite H \<and> (\<forall>j\<in>I - H. x j = 0\<^sub>(A j))")
 apply (rule allI) apply (rule impI) apply (erule conjE)+
 apply (subgoal_tac "\<forall>j\<in>I - H. prod_mOp I A x j = 0\<^sub>(A j)")
 apply blast
apply (rule ballI)
 apply (subgoal_tac "agroup (A j)") prefer 2 apply simp
 apply (subgoal_tac "x j = 0\<^sub>(A j)") prefer 2 apply simp
apply (subst prod_mOp_def) apply simp
 apply (rule ag_minus_0_eq_0) apply simp
done

lemma dsum_iOp_mem:"\<lbrakk>\<forall>j\<in>I. agroup (A j); X \<in> carr_dsumag I A\<rbrakk> \<Longrightarrow>
                         prod_mOp I A X \<in> carr_dsumag I A"
apply (frule dsum_iOp_func)
apply (simp add:funcset_mem)
done

lemma dsum_zero_func:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow>
                           prod_zero I A \<in> carr_dsumag I A"
apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
apply (rule conjI) apply (simp add:prod_zero_func)
 apply (subgoal_tac "{} \<subseteq> I") prefer 2 apply simp
 apply (subgoal_tac "finite {}") prefer 2 apply simp
 apply (subgoal_tac "\<forall>j\<in>I - {}. prod_zero I A j = 0\<^sub>A j")
 apply blast
 apply (rule ballI) apply simp
 apply (simp add:prod_zero_def)
done

lemma carrier_dsumag:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
         carrier (dsumag I A) = carr_dsumag I A"
apply (simp add:dsumag_def)
done

lemma dsumag_elemfun:"\<lbrakk>\<forall>k\<in>I. agroup (A k); f \<in> carrier (dsumag I A)\<rbrakk> \<Longrightarrow>
         f \<in> extensional I"
apply (simp add:carrier_dsumag)
apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
apply (erule conjE) apply (simp add:carr_prodag_def)
done

lemma dsumag_agroup:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> agroup (dsumag I A)"
apply (simp add:agroup_def [of "dsumag I A"])
apply (simp add:dsumag_def)  
apply (simp add:dsum_pOp_func)  
apply (simp add:dsum_iOp_func)
apply (simp add:dsum_zero_func)
apply (subgoal_tac "carr_dsumag I A \<subseteq> carr_prodag I A")
 prefer 2 apply (simp add:carr_dsumag_def) apply (simp add:finiteHom_def)
apply (rule subsetI) apply (simp add:CollectI)
apply (rule ballI)+
apply (rule conjI)
 apply (frule dsum_zero_func [of "I" "A"])
 apply (frule_tac X = "prod_zero I A" and Y = x in dsum_pOp_mem, assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (simp add:subsetD) apply (simp add:subsetD)
 apply (rule ballI)
 apply (simp add:prod_zero_def prod_pOp_def) apply (simp add:subsetD)
 apply (rule ag_l_zero) apply simp
 apply (frule_tac c = x in subsetD [of "carr_dsumag I A" "carr_prodag I A"],
                                                          assumption+)
 apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (frule dsum_zero_func [of "I" "A"])
 apply (frule_tac X = x in dsum_iOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = "(prod_mOp I A x)" and Y = x in 
            dsum_pOp_mem [of "I" "A"], assumption+) 
 apply (rule carr_prodag_mem_eq[of "I" "A"], assumption+)
 apply (simp add:subsetD)+
 apply (rule ballI)
 apply (simp add:prod_pOp_def prod_zero_def)
 apply (simp add:subsetD)+
 apply (simp add:prod_mOp_def) apply (simp add:subsetD)+
 apply (rule ag_l_inv1) apply simp
 apply (frule_tac c = x in subsetD [of "carr_dsumag I A" "carr_prodag I A"],
                                               assumption+)
 apply (simp add:carr_prodag_def)
apply (rule conjI)
 apply (frule_tac X = x and Y = y in dsum_pOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = "prod_pOp I A x y" and Y = z in dsum_pOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = y and Y = z in dsum_pOp_mem [of "I" "A"], assumption+)
 apply (frule_tac X = x and Y = "prod_pOp I A y z" in dsum_pOp_mem [of "I" "A"], assumption+) 
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (simp add:subsetD)+
 apply (rule ballI)
 apply (frule subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+)
 apply (frule_tac c = y in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+) 
 apply (frule_tac c = z in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+) 
 apply (frule_tac c = "prod_pOp I A x y" in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+) 
 apply (frule_tac c = " prod_pOp I A (prod_pOp I A x y) z" in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+) 
 apply (frule_tac c = "prod_pOp I A y z" in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+)
 apply (frule_tac c = "prod_pOp I A x (prod_pOp I A y z)" in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+)
 apply (frule_tac c = "prod_pOp I A y z" in subsetD[of "carr_dsumag I A" "carr_prodag I A"], assumption+)
 apply (thin_tac "prod_pOp I A x y \<in> carr_dsumag I A")
 apply (thin_tac "prod_pOp I A (prod_pOp I A x y) z \<in> carr_dsumag I A")
 apply (thin_tac "prod_pOp I A y z \<in> carr_dsumag I A")
 apply (thin_tac "prod_pOp I A x (prod_pOp I A y z) \<in> carr_dsumag I A")
 apply (simp add:prod_pOp_def) 
 apply (rule ag_pOp_assoc) apply simp
 apply (simp add:carr_prodag_def) apply (simp add:carr_prodag_def)
 apply (simp add:carr_prodag_def)
apply (frule_tac c = x in subsetD [of "carr_dsumag I A" "carr_prodag I A"],
                                               assumption+)
 apply (frule_tac c = y in subsetD [of "carr_dsumag I A" "carr_prodag I A"],
                                               assumption+)
 apply (rule carr_prodag_mem_eq [of "I" "A"], assumption+)
 apply (simp add:prod_pOp_mem)+
 apply (rule ballI)
 apply (simp add:prod_pOp_def)
 apply (rule ag_pOp_commute) apply simp
 apply (simp add:carr_prodag_def)+
done
  
lemma dsumag_pOp:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  pOp (dsumag I A) = prod_pOp I A"
apply (simp add:dsumag_def)
done

lemma dsumag_mOp:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  mOp (dsumag I A) = prod_mOp I A"
apply (simp add:dsumag_def)
done 

lemma dsumag_zero:"\<forall>k\<in>I. agroup (A k) \<Longrightarrow> 
                  zero (dsumag I A) = prod_zero I A"
apply (simp add:dsumag_def)
done

chapter "4. Ring theory"

section "1. Definition of a ring and an ideal"

record 'a RingType = "'a AgroupType" + 
  tOp      :: "['a, 'a ] \<Rightarrow> 'a"
  one     :: "'a"

constdefs

 ring :: "('a, 'more) RingType_scheme  \<Rightarrow> bool"
  "ring R  ==  agroup R \<and>(tOp R): carrier R \<rightarrow> carrier R \<rightarrow> carrier R \<and> 
  (one R) \<in>  carrier R  \<and> (\<forall> x \<in> carrier R. \<forall> y \<in> carrier R.
  \<forall> z \<in> carrier R. (tOp R (one R) x = x) \<and>
  (tOp R x (pOp R y z) = pOp R (tOp R x y) (tOp R x z)) \<and>
 (tOp R (tOp R x y) z = tOp R x (tOp R y z)) \<and> (tOp R x y = tOp R y x))"   

 unit ::"[('a, 'more) RingType_scheme, 'a] \<Rightarrow> bool"
  "unit R x == \<exists>y\<in> carrier R. x \<cdot>\<^sub>R y = 1\<^sub>R"

constdefs
 zeroring :: "('a, 'more) RingType_scheme \<Rightarrow> bool"
  "zeroring R == ring R \<and> carrier R = {0\<^sub>R}"

consts
  nscal ::  "('a, 'more) RingType_scheme  => 'a => nat  => 'a"
  npow   ::  "('a, 'more) RingType_scheme  => 'a => nat  => 'a"

  nsum0  :: "('a, 'more) RingType_scheme => (nat => 'a) => nat => 'a"
  eSum  :: "('a, 'more) AgroupType_scheme => (nat => 'a) => nat => 'a"
  nprod0  :: "('a, 'more) RingType_scheme => (nat => 'a) => nat => 'a"

primrec
 nscal_0:  "nscal R x 0 = 0\<^sub>R"
 nscal_suc:  "nscal R x (Suc n) = x +\<^sub>R (nscal R x n)"

primrec
  npow_0: "npow R x 0 = 1\<^sub>R"
  npow_suc: "npow R x (Suc n) = x \<cdot>\<^sub>R (npow R x n)" 

primrec
  nsum0_0: "nsum0 R f 0 = f 0"
  nsum0_suc: "nsum0 R f (Suc n) = f (Suc n) +\<^sub>R (nsum0 R f n)"

primrec
  eSum_0:"eSum R f 0 = f 0"
  eSum_Suc: "eSum R f (Suc n) = (eSum R f n) +\<^sub>R (f (Suc n))"

primrec
  nprod0_0: "nprod0 R f 0 = f 0"
  nprod0_suc: "nprod0 R f (Suc n) = (f (Suc n)) \<cdot>\<^sub>R (nprod0 R f n)"

syntax 
  "@NSCAL" :: "[nat, ('a, 'more) RingType_scheme, 'a] \<Rightarrow> 'a" 
       ("(3 _/ \<times>\<^sub>_ _)" [75,75,76]75)
  "@NPOW" ::  "['a, ('a, 'more) RingType_scheme, nat] \<Rightarrow>  'a" 
       ("(3_^\<^sup>_\<^sup> \<^sup>_)" [77,77,78]77)
  "@SUM" :: "('a, 'more) AgroupType_scheme => (nat => 'a) => nat => 'a"
       ("(3e\<Sigma> _ _ _)" [85,85,86]85)

translations
  "n \<times>\<^sub>R x" == "nscal R x n"
  "a^\<^sup>R\<^sup> \<^sup>n" == "npow R a n" 
  "e\<Sigma> G f n" == "eSum G f n"

constdefs
 subring::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> bool"
  "subring R S == S \<subseteq> carrier R \<and> 1\<^sub>R \<in> S \<and> (\<forall>x\<in>S. \<forall>y \<in> S. x +\<^sub>R (-\<^sub>R y) \<in> S \<and> x \<cdot>\<^sub>R y \<in> S)"

 Sr    ::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> 'a RingType"
  "Sr R S == \<lparr>carrier = S, pOp = \<lambda>x\<in>S. \<lambda>y\<in>S. x +\<^sub>R y, mOp = \<lambda>x\<in>S. -\<^sub>R x,
   zero = 0\<^sub>R, tOp = \<lambda>x\<in>S. \<lambda>y\<in>S. x \<cdot>\<^sub>R y, one = 1\<^sub>R \<rparr>"

lemma ring_is_ag:"ring R \<Longrightarrow> agroup R"
apply (simp add:ring_def)
done

lemma ring_zero:"ring R \<Longrightarrow> 0\<^sub>R \<in> carrier R"
apply (frule ring_is_ag[of "R"])
apply (simp add:agroup_def)
done

lemma ring_one:"ring R \<Longrightarrow> 1\<^sub>R \<in> carrier R"
apply (simp add:ring_def)
done

lemma ring_tOp_closed:"\<lbrakk>ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
                     x \<cdot>\<^sub>R y \<in> carrier R"
apply (subgoal_tac "tOp R \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R")
 prefer 2 apply (simp add:ring_def)
 apply (subgoal_tac "tOp R x \<in> carrier R \<rightarrow> carrier R")
 apply (rule funcset_mem, assumption+)+
done

lemma ring_tOp_commute:"\<lbrakk>ring R; x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow>
     x \<cdot>\<^sub>R y = y \<cdot>\<^sub>R x" 
apply (simp add:ring_def)
done

lemma ring_distrib1:"\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; 
 z \<in> carrier R \<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>R (y +\<^sub>R z) = x \<cdot>\<^sub>R y +\<^sub>R x \<cdot>\<^sub>R z"   
apply (simp add:ring_def)
done

lemma ring_distrib2:"\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; 
 z \<in> carrier R \<rbrakk> \<Longrightarrow> (y +\<^sub>R z) \<cdot>\<^sub>R x = y \<cdot>\<^sub>R x +\<^sub>R  z \<cdot>\<^sub>R x"   
apply (subgoal_tac "(y +\<^sub>R z) \<cdot>\<^sub>R x = x \<cdot>\<^sub>R (y +\<^sub>R z)") prefer 2
apply (rule ring_tOp_commute)
 apply assumption
 apply (rule ag_pOp_closed) apply (simp add:ring_def)
 apply assumption+
 apply simp
 apply (subgoal_tac "x \<cdot>\<^sub>R ( y +\<^sub>R z) = x \<cdot>\<^sub>R y +\<^sub>R x \<cdot>\<^sub>R z") 
 apply simp
apply (simp add: ring_tOp_commute)
 apply (simp add:ring_distrib1)
done

lemma ring_distrib3:"\<lbrakk>ring R; a \<in> carrier R; b \<in> carrier R;
x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> (a +\<^sub>R b) \<cdot>\<^sub>R (x +\<^sub>R y) = a \<cdot>\<^sub>R x +\<^sub>R 
a \<cdot>\<^sub>R y  +\<^sub>R b \<cdot>\<^sub>R x  +\<^sub>R b \<cdot>\<^sub>R y"
apply (subst ring_distrib2, assumption+)
apply (rule ag_pOp_closed) apply (simp add:ring_def)
 apply assumption+ 
apply (subst  ring_distrib1, assumption+)+ 
 apply (rule ag_pOp_assoc [THEN sym, of "R" "a \<cdot>\<^sub>R x +\<^sub>R a \<cdot>\<^sub>R y" "b \<cdot>\<^sub>R x" "b \<cdot>\<^sub>R y"])
 apply (simp add:ring_is_ag)
 apply (rule ag_pOp_closed)
 apply (simp add:ring_is_ag)
 apply (simp add:ring_tOp_closed)+
done

lemma rEQMulR:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; x = y \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R z = y \<cdot>\<^sub>R z"
  apply simp
  done

lemma ring_tOp_assoc:"\<lbrakk>ring R; x \<in> carrier R; y \<in> carrier R; 
 z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<cdot>\<^sub>R y) \<cdot>\<^sub>R z = x \<cdot>\<^sub>R (y \<cdot>\<^sub>R z)"
apply (simp add:ring_def)
done

lemma ring_l_one:"\<lbrakk> ring R; x \<in> carrier R \<rbrakk> \<Longrightarrow> 1\<^sub>R \<cdot>\<^sub>R x = x"
 apply (unfold ring_def)
 apply auto
done

lemma ring_r_one:"\<lbrakk> ring R; x \<in> carrier R \<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>R 1\<^sub>R = x"
 apply (subst ring_tOp_commute, assumption+)
 apply (simp add:ring_def)
 apply (simp add:ring_l_one)
done

lemma ring_times_0_x:"\<lbrakk> ring R; x \<in> carrier R \<rbrakk> \<Longrightarrow> 0\<^sub>R \<cdot>\<^sub>R x = 0\<^sub>R"
apply (frule ring_is_ag)
apply (frule ring_zero)
apply (frule ring_distrib2 [of "R" "x" "0\<^sub>R" "0\<^sub>R"], assumption+)
apply (simp add:ag_l_zero [of "R" "0\<^sub>R"])
apply (frule ring_tOp_closed [of "R" "0\<^sub>R" "x"], assumption+)
apply (frule sym) apply (thin_tac "0\<^sub>R \<cdot>\<^sub>R x =   0\<^sub>R \<cdot>\<^sub>R x +\<^sub>R  0\<^sub>R \<cdot>\<^sub>R x")
apply (frule ag_eq_sol2 [of "R" "0\<^sub>R \<cdot>\<^sub>R x" "0\<^sub>R \<cdot>\<^sub>R x" "0\<^sub>R \<cdot>\<^sub>R x"], assumption+)
apply (thin_tac "0\<^sub>R \<cdot>\<^sub>R x +\<^sub>R  0\<^sub>R \<cdot>\<^sub>R x =  0\<^sub>R \<cdot>\<^sub>R x")
apply (simp add:ag_r_inv1)
done


lemma ring_times_x_0:"\<lbrakk>ring R; x \<in> carrier R\<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>R 0\<^sub>R = 0\<^sub>R"
apply (frule ring_zero)
apply (subst ring_tOp_commute, assumption+) apply (simp add:ring_zero)
apply (simp add:ring_times_0_x)
done 

lemma rMulZeroDiv:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; x = 0\<^sub>R \<or> y = 0\<^sub>R \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R y = 0\<^sub>R";
apply auto
apply (rule ring_times_0_x, assumption+)
apply (rule ring_times_x_0, assumption+)
done

lemma ring_inv1:"\<lbrakk> ring R; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
      -\<^sub>R (a \<cdot>\<^sub>R b) = (-\<^sub>R a) \<cdot>\<^sub>R b \<and> -\<^sub>R (a \<cdot>\<^sub>R b) = a \<cdot>\<^sub>R (-\<^sub>R b)"
apply (frule ring_is_ag)  
apply (rule conjI) 
apply (frule ring_distrib2 [THEN sym, of "R" "b" "a" "-\<^sub>R a"], assumption+)
 apply (frule ag_mOp_closed [of "R" "a"], assumption+)
 apply (simp add:ag_r_inv1 [of "R" "a"])
 apply (simp add:ring_times_0_x)
 apply (frule ag_mOp_closed [of "R" "a"], assumption+)
 apply (frule ring_tOp_closed [of "R" "a" "b"], assumption+)
 apply (frule ring_tOp_closed [of "R" "-\<^sub>R a" "b"], assumption+)
 apply (frule ag_eq_sol1 [of "R" "a \<cdot>\<^sub>R b" "(-\<^sub>R a) \<cdot>\<^sub>R b" "0\<^sub>R"], assumption+)
 apply (rule ring_zero, assumption+)
 apply (thin_tac " a \<cdot>\<^sub>R b +\<^sub>R  (-\<^sub>R a) \<cdot>\<^sub>R b = 0\<^sub>R") 
 apply (frule sym) apply (thin_tac "(-\<^sub>R a) \<cdot>\<^sub>R b =  -\<^sub>R  a \<cdot>\<^sub>R b +\<^sub>R 0\<^sub>R")
 apply (frule ag_mOp_closed [of "R" " a \<cdot>\<^sub>R b"], assumption+)
 apply (simp add:ag_r_zero)
apply (frule ring_distrib1 [THEN sym, of "R" "a" "b" "-\<^sub>R b"], assumption+)
 apply (simp add:ag_mOp_closed)
  apply (simp add:ag_r_inv1 [of "R" "b"])
  apply (simp add:ring_times_x_0)
 apply (frule ag_mOp_closed [of "R" "b"], assumption+)
 apply (frule ring_tOp_closed [of "R" "a" "b"], assumption+)
 apply (frule ring_tOp_closed [of "R" "a" "-\<^sub>R b"], assumption+)
 apply (frule ag_eq_sol1 [THEN sym, of "R" "a \<cdot>\<^sub>R b" "a \<cdot>\<^sub>R (-\<^sub>R b)" "0\<^sub>R"], 
                                                      assumption+)
 apply (simp add:ring_zero) apply assumption
 apply (frule ag_mOp_closed [of "R" " a \<cdot>\<^sub>R b"], assumption+)
  apply (simp add:ag_r_zero)
done

lemma ring_inv1_1:"\<lbrakk> ring R; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
      -\<^sub>R (a \<cdot>\<^sub>R b) = (-\<^sub>R a) \<cdot>\<^sub>R b"
apply (simp add:ring_inv1)
done

lemma ring_inv1_2:"\<lbrakk> ring R; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
                                -\<^sub>R (a \<cdot>\<^sub>R b) = a \<cdot>\<^sub>R (-\<^sub>R b)"
apply (frule ring_inv1 [of "R" "a" "b"], assumption+)
apply (frule conj_2) 
apply (thin_tac " -\<^sub>R  a \<cdot>\<^sub>R b =  (-\<^sub>R a) \<cdot>\<^sub>R b \<and> -\<^sub>R  a \<cdot>\<^sub>R b =  a \<cdot>\<^sub>R (-\<^sub>R b)")
apply simp
done

lemma ring_times_minusl:"\<lbrakk>ring R; a \<in> carrier R\<rbrakk> \<Longrightarrow>  -\<^sub>R a = (-\<^sub>R 1\<^sub>R) \<cdot>\<^sub>R a"
apply (frule ring_one[of "R"])
apply (frule ring_inv1_1[of "R" "1\<^sub>R" "a"], assumption+)
apply (simp add:ring_l_one)
done

lemma ring_times_minusr:"\<lbrakk>ring R; a \<in> carrier R\<rbrakk> \<Longrightarrow>  -\<^sub>R a = a \<cdot>\<^sub>R (-\<^sub>R 1\<^sub>R)"
apply (frule ring_one[of "R"])
apply (frule ring_inv1_2[of "R" "a" "1\<^sub>R"], assumption+)
apply (simp add:ring_r_one)
done

lemma ring_inv1_3:"\<lbrakk> ring R; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow>
                           a \<cdot>\<^sub>R b = (-\<^sub>R a) \<cdot>\<^sub>R (-\<^sub>R b)"
apply (frule ring_is_ag)
apply (subst  ag_inv_inv[THEN sym], assumption)
apply (simp add:ag_mOp_closed ring_tOp_closed)
apply (subst ring_inv1_1, assumption+)
apply (simp add:ag_mOp_closed)+
apply (simp add:ag_inv_inv)
apply (subst ring_inv1_2, assumption+)
apply (simp add:ag_mOp_closed)
apply (simp add:ag_inv_inv)
done

lemma ring_distrib4:"\<lbrakk>ring R; a \<in> carrier R; b \<in> carrier R;
x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>R b +\<^sub>R (-\<^sub>R x \<cdot>\<^sub>R y) =
                      a \<cdot>\<^sub>R (b +\<^sub>R (-\<^sub>R y)) +\<^sub>R (a +\<^sub>R (-\<^sub>R x)) \<cdot>\<^sub>R y"
apply (frule ring_is_ag)
apply (subst ring_distrib1, assumption+)
apply (rule ag_mOp_closed, assumption+) 
apply (subst ring_distrib2, assumption+)
apply (rule ag_mOp_closed, assumption+) 
apply (subst pOp_assocTr43, assumption+)
apply (rule ring_tOp_closed, assumption+)+
 apply (rule ag_mOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)+
 apply (simp add:ag_mOp_closed)+
apply (subst ring_distrib1 [THEN sym, of "R" "a" _], assumption+)
 apply (rule ag_mOp_closed, assumption+)
apply (simp add:ag_l_inv1)
apply (simp add:ring_times_x_0)
apply (subst ag_r_zero, assumption+)
apply (simp add:ring_tOp_closed)
apply (simp add: ring_inv1_1)
done

lemma rMulLC:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R (y \<cdot>\<^sub>R z) = y \<cdot>\<^sub>R (x \<cdot>\<^sub>R z)"
  apply (subst ring_tOp_assoc [THEN sym], assumption+)
  apply (subst ring_tOp_commute [of "R" "y" "x"], assumption+)
  apply (subst ring_tOp_assoc, assumption+)
  apply (rule refl)
  done 

lemma Zero_ring:"\<lbrakk> ring R; 1\<^sub>R = 0\<^sub>R \<rbrakk> \<Longrightarrow> zeroring R"
apply (subgoal_tac "carrier R = {0\<^sub>R}") apply (simp add:zeroring_def)
apply (rule equalityI)
apply (rule subsetI)
apply (subgoal_tac "x \<cdot>\<^sub>R 1\<^sub>R = x \<cdot>\<^sub>R 0\<^sub>R")
apply (subgoal_tac "x = x \<cdot>\<^sub>R 1\<^sub>R") apply (subgoal_tac "x \<cdot>\<^sub>R 0\<^sub>R = 0\<^sub>R")
apply simp
apply (subgoal_tac "x \<cdot>\<^sub>R 0\<^sub>R = 0\<^sub>R \<cdot>\<^sub>R x") apply simp
apply (simp add:ring_times_0_x) apply (simp add:ring_def)
 apply (thin_tac "1\<^sub>R = 0\<^sub>R") (** important **)
apply (rule ring_r_one[THEN sym])  apply assumption+ apply simp
apply (simp add:ring_def)
done

lemma Zero_ring1:"\<lbrakk> ring R; \<not> (zeroring R)\<rbrakk> \<Longrightarrow>  1\<^sub>R \<noteq> 0\<^sub>R "
apply (rule contrapos_pp) apply simp+
apply (frule Zero_ring, assumption+)
apply simp
done

lemma Sr_one:"\<lbrakk>ring R; subring R S\<rbrakk> \<Longrightarrow> 1\<^sub>R \<in> S"
apply (simp add:subring_def)
done

lemma Sr_zero:"\<lbrakk>ring R; subring R S\<rbrakk> \<Longrightarrow> 0\<^sub>R \<in> S"
apply (frule Sr_one[of "R" "S"], assumption+)
apply (simp add:subring_def) apply (erule conjE)+
 apply (subgoal_tac "(1\<^sub>R) +\<^sub>R (-\<^sub>R (1\<^sub>R)) \<in> S") prefer 2 apply simp
 apply (frule subsetD[of "S" "carrier R" "1\<^sub>R"], assumption+)
 apply (frule ring_is_ag[of "R"])
 apply (simp add:ag_r_inv1)
done

lemma Sr_mOp_closed:"\<lbrakk>ring R; subring R S; x \<in> S\<rbrakk> \<Longrightarrow> -\<^sub>R x \<in> S" 
apply (frule Sr_zero[of "R" "S"], assumption+)
apply (simp add:subring_def) apply (erule conjE)+
 apply (subgoal_tac "0\<^sub>R +\<^sub>R (-\<^sub>R x) \<in> S")
 apply (frule subsetD[of "S" "carrier R" "0\<^sub>R"], assumption+)
 apply (frule subsetD[of "S" "carrier R" "x"], assumption+)
 apply (frule ring_is_ag [of "R"])
 apply (thin_tac "\<forall>x\<in>S. \<forall>y\<in>S.  x +\<^sub>R -\<^sub>R y \<in> S \<and> RingType.tOp R x y \<in> S")
 apply (frule ag_mOp_closed [of "R" "x"]) apply (simp add:subsetD)
 apply (simp add:ag_l_zero) apply simp
done

lemma Sr_pOp_closed:"\<lbrakk>ring R; subring R S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x +\<^sub>R y \<in> S"
apply (frule Sr_mOp_closed[of "R" "S" "y"], assumption+)
apply (unfold subring_def) apply (erule conjE)+
 apply (subgoal_tac "x +\<^sub>R (-\<^sub>R (-\<^sub>R y)) \<in> S")
 apply (frule ring_is_ag [of "R"])
 apply (thin_tac "\<forall>x\<in>S. \<forall>y\<in>S.  x +\<^sub>R -\<^sub>R y \<in> S \<and> RingType.tOp R x y \<in> S")
 apply (frule subsetD[of "S" "carrier R" "y"], assumption+)
 apply (simp add:ag_inv_inv) apply simp
done

lemma Sr_tOp_closed:"\<lbrakk>ring R; subring R S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>R y \<in> S"
apply (simp add:subring_def)
done

lemma Sr_ring:"\<lbrakk>ring R; subring R S\<rbrakk> \<Longrightarrow> ring (Sr R S)"
apply (simp add:ring_def [of "Sr R S"])
 apply (rule conjI)
 prefer 2
 apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+ apply (simp add:Sr_def) apply (simp add:subring_def)
 apply (rule conjI)
  apply (simp add:Sr_def subring_def)
 apply (rule ballI)+
  apply (subgoal_tac "S \<subseteq> carrier R")
  apply (simp add:Sr_def Sr_tOp_closed Sr_pOp_closed Sr_one)
  apply (frule_tac c = x in subsetD[of "S" "carrier R"], assumption+)
  apply (frule_tac c = y in subsetD[of "S" "carrier R"], assumption+)
  apply (frule_tac c = z in subsetD[of "S" "carrier R"], assumption+)
  apply (simp add:ring_l_one)
  apply (simp add:ring_distrib1)
  apply (simp add:ring_tOp_assoc)
  apply (simp add:ring_tOp_commute) apply (simp add:subring_def)
 apply (simp add:agroup_def)
 apply (rule conjI)
  apply (rule bivar_func_test)
  apply (rule ballI)+
  apply (simp add:Sr_def) apply (simp add:Sr_pOp_closed)
 apply (rule conjI)
  apply (rule univar_func_test)
  apply (rule ballI)
  apply (simp add:Sr_def) apply (simp add:Sr_mOp_closed)
 apply (rule conjI)
  apply (simp add:Sr_def) apply (simp add:Sr_zero)
apply (rule ballI)+
 apply (simp add:Sr_def Sr_pOp_closed Sr_mOp_closed Sr_zero)
  apply (subgoal_tac "S \<subseteq> carrier R")
  apply (frule_tac c = x in subsetD[of "S" "carrier R"], assumption+)
  apply (frule_tac c = y in subsetD[of "S" "carrier R"], assumption+)
  apply (frule_tac c = z in subsetD[of "S" "carrier R"], assumption+)
 apply (frule ring_is_ag[of "R"])
  apply (simp add:ag_l_zero)
  apply (simp add:ag_l_inv1)
  apply (simp add:ag_pOp_assoc)
  apply (simp add:ag_pOp_commute)
apply (simp add:subring_def)
done

section "2. Calculation of elements"
 (** The author of this part is L. Chen, revised by H. Murao in Isar
     and proof modified by Y. Santo **)

subsection "nscale"

lemma ring_tOp_rel:"\<lbrakk>ring R; x\<in>carrier R; xa\<in>carrier R; y\<in>carrier R;
ya \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<cdot>\<^sub>R xa) \<cdot>\<^sub>R (y \<cdot>\<^sub>R ya) = (x \<cdot>\<^sub>R y) \<cdot>\<^sub>R (xa \<cdot>\<^sub>R ya)"
apply (subgoal_tac "x \<cdot>\<^sub>R xa \<cdot>\<^sub>R ( y \<cdot>\<^sub>R ya) = x \<cdot>\<^sub>R (xa \<cdot>\<^sub>R  (y \<cdot>\<^sub>R ya))")
apply simp apply (subgoal_tac "xa \<cdot>\<^sub>R ( y \<cdot>\<^sub>R ya) = xa \<cdot>\<^sub>R  y \<cdot>\<^sub>R ya") 
apply simp apply (subgoal_tac "xa \<cdot>\<^sub>R y = y \<cdot>\<^sub>R xa") apply simp
apply (subgoal_tac "y \<cdot>\<^sub>R xa \<cdot>\<^sub>R ya = y \<cdot>\<^sub>R (xa \<cdot>\<^sub>R ya)") apply simp
apply (rule ring_tOp_assoc [THEN sym]) apply assumption+ 
apply (simp add:ring_tOp_closed) apply (simp add:ring_tOp_assoc)
apply (simp add:ring_tOp_commute)
apply (simp add:ring_tOp_assoc [THEN sym]) 
apply (subgoal_tac "y \<cdot>\<^sub>R ya \<in> carrier R")
apply (simp add:ring_tOp_assoc [of "R" "x" "xa" "y \<cdot>\<^sub>R ya"])
apply (simp add:ring_tOp_closed)
done


lemma nsClose:
  "\<And> n. \<lbrakk> ring R; x \<in> carrier R \<rbrakk>  \<Longrightarrow> nscal R x n \<in> carrier R"
  apply (induct_tac n)
  apply simp
  apply (simp add:ring_def agroup_def)
  apply simp
  apply (rule ag_pOp_closed) apply (simp add:ring_def) apply assumption+
  done

lemma nsZero:
  "ring R \<Longrightarrow> nscal R (0\<^sub>R) n = (0\<^sub>R)"
  apply (induct_tac n)
  apply simp

  apply (subst nscal_suc)  (*** "apply simp" is enough ***) 
    apply simp
  apply (rule ag_r_zero) apply (simp add:ring_def)
  apply (simp add:ring_def agroup_def)
  done  

lemma nsZeroI: "\<And> n. \<lbrakk> ring R; x = 0\<^sub>R \<rbrakk> \<Longrightarrow> nscal R x n = 0\<^sub>R";
  apply (simp only:nsZero)
  done

lemma nsEqElm:  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R; x = y \<rbrakk>
	\<Longrightarrow> (nscal R x n) = (nscal R y n)"
  apply simp
  done

lemma nsDistr:  "\<lbrakk> ring R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> (nscal R x n) +\<^sub>R (nscal R x m) = nscal R x (n + m)"
  apply (induct_tac n)
  apply simp apply (rule ag_l_zero) apply (simp add:ring_def)
 
  apply (simp add:nsClose) 
  apply simp   
  apply (subst ag_pOp_assoc) apply (simp add:ring_def) apply assumption+
  apply (simp add:nsClose)+
  done

lemma nsDistrL:  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk>
	\<Longrightarrow> (nscal R x n) +\<^sub>R (nscal R y n) = nscal R (x +\<^sub>R y) n"
  apply (frule ring_is_ag)
  apply (induct_tac n)
  apply simp 
  apply (rule ag_l_zero) apply assumption apply (simp add:agroup_def)

  apply simp
  apply (subgoal_tac "x +\<^sub>R  n \<times>\<^sub>R x +\<^sub>R ( y +\<^sub>R  n \<times>\<^sub>R y) 
          = x +\<^sub>R  (n \<times>\<^sub>R x +\<^sub>R ( y +\<^sub>R  n \<times>\<^sub>R y))") apply simp
  apply (subgoal_tac " n \<times>\<^sub>R x +\<^sub>R ( y +\<^sub>R  n \<times>\<^sub>R y) =  n \<times>\<^sub>R x +\<^sub>R  y +\<^sub>R  n \<times>\<^sub>R y")
  apply simp apply (subgoal_tac "n \<times>\<^sub>R x +\<^sub>R y = y +\<^sub>R n \<times>\<^sub>R x") apply simp
  apply (subgoal_tac "y +\<^sub>R  n \<times>\<^sub>R x +\<^sub>R  n \<times>\<^sub>R y =  y +\<^sub>R  (n \<times>\<^sub>R x +\<^sub>R  n \<times>\<^sub>R y)")
  apply simp apply (rule ag_pOp_assoc [THEN sym]) apply assumption+
   apply (rule nsClose) apply assumption+ apply (simp add:ag_pOp_closed)
   apply (rule ag_pOp_assoc) apply assumption+ apply (rule nsClose)
   apply assumption+ apply (simp add:nsClose)
   apply (rule ag_pOp_commute) apply assumption apply (rule nsClose)
   apply assumption+
  apply (rule ag_pOp_assoc [THEN sym]) apply assumption+ 
  apply (rule nsClose) apply assumption+
  apply (rule nsClose) apply assumption+ 
  apply (rule ag_pOp_assoc) apply assumption+
  apply (rule nsClose, assumption+)
  apply (rule ag_pOp_closed) apply assumption+ apply (rule nsClose)
  apply assumption+
done

lemma nsMulDistrL:  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R (nscal R y n) = nscal R (x \<cdot>\<^sub>R y) n";
  apply (induct_tac n)
  apply simp
  apply (simp add:ring_times_x_0)

  apply simp apply (subst ring_distrib1) apply assumption+
  apply (rule nsClose) apply assumption+
  apply simp
done
 
lemma nsMulDistrR:  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk>
	\<Longrightarrow> (nscal R y n) \<cdot>\<^sub>R x = nscal R (y \<cdot>\<^sub>R x) n"
  apply (subgoal_tac "n \<times>\<^sub>R y \<cdot>\<^sub>R x = x \<cdot>\<^sub>R (n \<times>\<^sub>R y)") apply simp
  apply (simp add:nsMulDistrL [of "R" "x" "y"])
  apply (simp add:ring_tOp_commute)
  apply (rule ring_tOp_commute) apply assumption apply (rule nsClose)
   apply assumption+
done

subsection "npow"

lemma npClose:"\<lbrakk> ring R; x \<in> carrier R \<rbrakk> \<Longrightarrow> npow R x n \<in> carrier R"
  apply (induct_tac n)
  apply simp apply (simp add:ring_def)

  apply simp
  apply (rule ring_tOp_closed) apply assumption+
  done

lemma npMulDistr:"\<And> n m.\<lbrakk> ring R; x \<in> carrier R\<rbrakk>
  \<Longrightarrow> (npow R x n) \<cdot>\<^sub>R (npow R x m) = npow R x (n + m)" 
  apply (induct_tac m)
  apply simp apply (rule ring_r_one)
   apply assumption  apply (simp add:npClose)
  apply (subgoal_tac "n + Suc na = Suc (n + na)") apply simp
  apply (subst ring_tOp_assoc [THEN sym]) apply assumption
   apply (simp add:npClose) apply assumption 
   apply (simp add:npClose)
   apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>n \<cdot>\<^sub>R x = x \<cdot>\<^sub>R x^\<^sup>R\<^sup> \<^sup>n") apply simp
  apply (subst ring_tOp_assoc, assumption+)
   apply (simp add:npClose)+ apply (rule ring_tOp_commute, assumption+)
   apply (rule npClose, assumption+) 
   apply simp
done

lemma npMulExp:"\<And>n m. \<lbrakk> ring R; x \<in> carrier R \<rbrakk>
        \<Longrightarrow>  npow R (npow R x n) m = npow R x (n * m)" (* You Santo *)
apply (induct_tac m)
apply simp
apply simp
apply (simp add:npMulDistr)
done    


lemma npGTPowZero_sub:
  " \<And> n. \<lbrakk> ring R; x \<in> carrier R; npow R x m = 0\<^sub>R\<rbrakk>
	\<Longrightarrow>(m \<le> n) \<longrightarrow> (npow R x n = 0\<^sub>R)";
  apply (rule impI)
  apply (subgoal_tac "npow R x n = (npow R x (n-m)) \<cdot>\<^sub>R (npow R x m)")
  apply simp
  apply (rule ring_times_x_0) apply assumption apply (simp add:npClose)
  apply (thin_tac "x^\<^sup>R\<^sup> \<^sup>m = 0\<^sub>R")
  apply (subgoal_tac "n = n - m + m")
  apply (subgoal_tac "npow R x n = npow R x ((n - m) + m)")
  apply (subgoal_tac "npow R x ((n-m) + m) = (npow R x (n-m)) \<cdot>\<^sub>R (npow R x m)")
   apply simp apply (rule npMulDistr [THEN sym], assumption+) 
   apply simp apply simp
  done

lemma npGTPowZero:
  "\<And> n. \<lbrakk> ring R; x \<in> carrier R; npow R x m = 0\<^sub>R; m \<le> n \<rbrakk>
	\<Longrightarrow> npow R x n = 0\<^sub>R";
  apply (subgoal_tac "npow R x n = npow R x (n - m) \<cdot>\<^sub>R (npow R x m)")
  apply simp
  apply (rule ring_times_x_0) apply assumption
    apply (simp add: npClose)
  apply (subgoal_tac "npow R x n = npow R x ((n - m) + m)")
  apply (subgoal_tac "npow R x ((n-m) + m) = (npow R x (n-m)) \<cdot>\<^sub>R (npow R x m)")
   apply simp apply (rule  npMulDistr [THEN sym]) apply assumption+
   apply simp
  done


lemma npOne: "\<And> n. ring R  \<Longrightarrow> npow R (1\<^sub>R) n = 1\<^sub>R"
  apply (induct_tac n) apply simp

  apply simp
    apply (rule ring_r_one) apply assumption 
    apply (simp add:ring_def)
done

lemma npZero_sub: "\<And> n. ring R \<Longrightarrow> 0 < n \<longrightarrow> npow R (0\<^sub>R) n = 0\<^sub>R"
  apply (induct_tac "n")
  apply simp

  apply simp
    apply (rule ring_times_0_x) apply assumption
    apply (rule npClose) apply assumption
    apply (simp add:ring_def agroup_def)
done

lemma npZero: "\<lbrakk> ring R; 0 < n \<rbrakk> \<Longrightarrow> npow R (0\<^sub>R) n = 0\<^sub>R"
  apply (simp add:npZero_sub)
done
 
lemma npMulElmL: "\<And> n. \<lbrakk> ring R; x \<in> carrier R; 0 \<le> n\<rbrakk> 
        \<Longrightarrow> x \<cdot>\<^sub>R (npow R x n) = npow R x (Suc n)"
apply (simp only:npow_suc)
done

lemma npMulEleL: "\<And> n. \<lbrakk> ring R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> (npow R x n) \<cdot>\<^sub>R x =  npow R x (Suc n)"
  apply (simp only:npow_suc)
  apply (rule ring_tOp_commute) apply assumption
  apply (rule npClose) apply assumption+
done


lemma npMulElmR: "\<And> n. \<lbrakk> ring R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> (npow R x n) \<cdot>\<^sub>R x =  npow R x (Suc n)"
  apply (induct_tac "n")
  apply (subst npow_suc)
    apply (rule ring_tOp_commute, assumption+)
      apply (rule npClose, assumption+)

  apply simp apply (subst ring_tOp_assoc, assumption+)
    apply (simp add:npClose) apply assumption
    apply (simp add: ring_tOp_commute)
  done

lemma np_1:"\<lbrakk>ring R; a \<in> carrier R\<rbrakk> \<Longrightarrow> npow R a (Suc 0) = a"  (* Y. Santo*)
apply simp
 apply (simp add:ring_r_one)
done
 
subsection  "nsum0"

lemma nsumClose: "\<And> n. \<lbrakk> ring R; range f \<subseteq> carrier R \<rbrakk>
           \<Longrightarrow> nsum0 R f n \<in> carrier R"
  apply (induct_tac "n")
  apply auto

  apply (rule ag_pOp_closed) apply (simp add:ring_def)
  apply auto
  done  

lemma nsumElmClose: "\<And> n. \<lbrakk>ring R; \<forall>i. f i \<in> carrier R\<rbrakk> \<Longrightarrow> 
                             nsum0 R f n \<in> carrier R"
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (rule ag_pOp_closed) apply (simp add:ring_def)
  apply simp+
done

lemma nsumMulEleL: "\<And> n. \<lbrakk> ring R; \<forall> i. f i \<in> carrier R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R (nsum0 R f n) = nsum0 R (\<lambda> i. x \<cdot>\<^sub>R (f i)) n"
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (subst ring_distrib1, assumption+) apply simp+
  apply (rule nsumClose) 
apply auto
done 

lemma nsumMulElmL:
  "\<And> n. \<lbrakk> ring R; \<forall> i. f i \<in> carrier R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> x \<cdot>\<^sub>R (nsum0 R f n) = nsum0 R (\<lambda> i. x \<cdot>\<^sub>R (f i)) n"
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (subst ring_distrib1, assumption+)
    apply (simp add:nsumElmClose)+
  done

lemma nsumTail:
  "\<lbrakk> ring R; range f \<subseteq> carrier R \<rbrakk>
	\<Longrightarrow> nsum0 R f (Suc n) = (nsum0 R (\<lambda> i. (f (Suc i))) n) +\<^sub>R (f 0)"
 apply (induct_tac "n")
  apply simp

  apply simp
    apply (rule ag_pOp_assoc [THEN sym]) apply (simp add:ring_def)
    apply auto apply (rule nsumClose, assumption+)
    apply auto
  done

lemma nsumElmTail:
  "\<lbrakk> ring R; \<forall>i. f i \<in> carrier R \<rbrakk>
	\<Longrightarrow> nsum0 R f (Suc n) = (nsum0 R (\<lambda> i. (f (Suc i))) n) +\<^sub>R (f 0)"
  apply (induct_tac n)
  apply simp

  apply simp
    apply (rule ag_pOp_assoc [THEN sym]) apply (simp add:ring_def)
    apply simp apply (rule nsumClose, assumption+)
    apply auto
done
  

lemma nsumAdd:
  "\<lbrakk> ring R; range f \<subseteq> carrier R; range g \<subseteq> carrier R \<rbrakk>
  \<Longrightarrow> nsum0 R (\<lambda> i. (f i) +\<^sub>R (g i)) n = (nsum0 R f n) +\<^sub>R (nsum0 R g n)"
  apply (induct_tac "n")
  apply simp

  apply simp 
  apply (rule ag_add4_rel) apply (simp add:ring_def)
  apply auto apply (rule nsumClose) apply assumption
    apply auto apply (rule nsumClose) apply assumption
    apply auto
  done

lemma nsumElmAdd:
  "\<lbrakk> ring R; \<forall> i. f i \<in> carrier R; \<forall> i. g i \<in> carrier R \<rbrakk>
	\<Longrightarrow> nsum0 R (\<lambda> i. (f i) +\<^sub>R (g i)) n
		= (nsum0 R f n) +\<^sub>R (nsum0 R g n) "
  apply (induct_tac "n")
  apply simp

  apply simp
  apply (rule ag_add4_rel) apply (simp add:ring_def) apply simp+
  apply (rule nsumClose) apply assumption+
  apply auto apply (rule nsumClose, assumption+) apply auto
  done      (*remark: range is the image of UNIV *)

lemma npeSum2_sub_muly:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
	y \<cdot>\<^sub>R(nsum0 R (\<lambda>i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>R (npow R y i))
				(n choose i)) n)
    	= nsum0 R (\<lambda>i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>R (npow R y (i+1)))
				(n choose i)) n"
  apply (subst nsumMulElmL, assumption)
    apply (rule allI)
      apply (simp only:nsClose add:ring_tOp_closed 
             add:npClose)
    apply assumption
  apply (simp only:nsMulDistrL add:nsClose add:ring_tOp_closed
         add:npClose)  
  apply (simp only: rMulLC [of "R" "y"] add:npClose)

  apply (simp only: npow_suc [THEN sym, of "R" "y"])
  apply simp
  done

(********)(********)(********)(********)
lemma binomial_n0: "(Suc n choose 0) = (n choose 0)";
  apply (simp)
  done

lemma binomial_ngt_diff:
  "(n choose Suc n) = (Suc n choose Suc n) - (n choose n)";
  apply (subst binomial_Suc_Suc)
  apply (arith)
  done

lemma binomial_ngt_0: "(n choose Suc n) = 0";
  apply (subst binomial_ngt_diff)
  apply (subst binomial_n_n)+
  apply (simp)
  done

lemma diffLessSuc: "m \<le> n \<Longrightarrow> Suc (n-m) = Suc n - m";
  apply (arith)
  done

lemma npow_suc_i:
  "\<lbrakk> ring R; x \<in> carrier R; i \<le> n \<rbrakk>
	\<Longrightarrow> npow R x (Suc n - i) =  x \<cdot>\<^sub>R (npow R x (n-i))"
  apply (subst diffLessSuc [THEN sym, of "i" "n"], assumption)
  apply (rule npow_suc)
  done


lemma nsumEqFunc_sub:
  "\<lbrakk>  ring R; \<And> i. f i \<in> carrier R; \<And> i. g i \<in> carrier R \<rbrakk>
	\<Longrightarrow> ( \<forall> i. i \<le> n \<longrightarrow> f i = g i) \<longrightarrow> (nsum0 R f n = nsum0 R g n)";
  apply (induct_tac "n")
  apply (simp)
  apply (simp)
  done

lemma nsumEqFunc:
  "\<lbrakk> ring R; \<And> i. f i \<in> carrier R; \<And> i. g i \<in> carrier R;
     \<And> i. i \<le> n \<longrightarrow> f i = g i \<rbrakk> \<Longrightarrow>  nsum0 R f n = nsum0 R g n"
  apply (frule nsumEqFunc_sub [of "R" "f" "g" "n"])
  apply (simp)
  apply (simp)
  apply (simp)
  done
(********)(********)

lemma npeSum2_sub_mulx: "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
  x \<cdot>\<^sub>R (nsum0 R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>R (npow R y i)) 
                                                        (n choose i)) n)
   = (nsum0 R (\<lambda>i. nscal R
			  ((npow R x (Suc n - Suc i)) \<cdot>\<^sub>R (npow R y (Suc i)))
			  (n choose Suc i)) n) +\<^sub>R
		(nscal R ((npow R x (Suc n - 0)) \<cdot>\<^sub>R (npow R y 0))
			(Suc n choose 0))"
  apply (rule sym, rule trans)
  apply (simp only: binomial_n0)
  apply (subst nsumElmTail [THEN sym, of "R" "\<lambda> i. nscal R ((npow R x (Suc n - i)) \<cdot>\<^sub>R (npow R y i)) (n choose i)"])
    apply (assumption)
    apply (rule allI)
      apply (simp only:nsClose add:ring_tOp_closed add:npClose)

  apply (simp only:nsum0_suc)
  apply (subst binomial_ngt_0)
  apply (simp only:nscal_0)
  apply (subst ring_is_ag [THEN ag_l_zero], assumption)
    apply (simp add:nsumElmClose nsClose ring_tOp_closed npClose)
 
  apply (subst nsumMulElmL [of "R" _ "x"], assumption)
    apply (rule allI, rule nsClose, assumption, rule ring_tOp_closed, assumption+, rule npClose, assumption+)
    apply (rule npClose, assumption+)

  apply (simp add: nsMulDistrL [of "R" "x"] ring_tOp_closed npClose)
  apply (simp add:ring_tOp_assoc [THEN sym, of "R" "x"] add:npClose)

  apply (rule nsumEqFunc, assumption)
    apply (rule nsClose, assumption+, rule ring_tOp_closed, assumption+, (rule npClose, assumption+)+)
    apply (rule nsClose, assumption+, (rule ring_tOp_closed, assumption+)+, (rule npClose, assumption+)+)

  apply (rule impI)
  apply (rule nsEqElm, assumption)
    apply (rule ring_tOp_closed, assumption+, (rule npClose, assumption+)+)
    apply ((rule ring_tOp_closed, assumption+)+, (rule npClose, assumption+)+)
   
  apply (rule rEQMulR, assumption+)
    apply (rule npClose, assumption+)
    apply (rule ring_tOp_closed, assumption+, rule npClose, assumption+)
    apply (rule npClose, assumption+)

  apply (rule npow_suc_i, assumption+)
  done

lemma npeSum2_sub_mulx2:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
	x \<cdot>\<^sub>R (nsum0 R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>R (npow R y i))
				(n choose i)) n)
	= (nsum0 R  (\<lambda>i. nscal R
			  ((npow R x (n - i)) \<cdot>\<^sub>R (y \<cdot>\<^sub>R (npow R y i)))
			  (n choose Suc i)) n) +\<^sub>R
		(((x \<cdot>\<^sub>R (npow R x n)) \<cdot>\<^sub>R (1\<^sub>R)) +\<^sub>R (0\<^sub>R))"
  apply (subst npeSum2_sub_mulx, assumption+)
  apply (simp)
  done

lemma npeSum2:
  "\<And> n. \<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk>
	\<Longrightarrow> npow R (x +\<^sub>R y) n =
		nsum0 R (\<lambda> i. nscal R ((npow R x (n-i)) \<cdot>\<^sub>R (npow R y i))
				       ( n choose i) ) n"
  apply (frule ring_is_ag)
  apply (induct_tac "n")

  (*1*)
  apply (simp)
    apply (subst ring_r_one, assumption+) apply (simp add:ring_def)
      apply (rule ag_r_zero [THEN sym], assumption+) apply (simp add:ring_def)
  (*1:done*)

  apply (subst nsumElmTail, assumption+)
    apply (simp add:nsumElmClose)+
    apply (rule allI)
    apply (simp add:nsClose ring_tOp_closed npClose)

(**
thm binomial_Suc_Suc
**)
  apply (simp only:binomial_Suc_Suc)
  apply (simp only: nsDistr [THEN sym] add:npClose ring_tOp_closed)
  apply (subst nsumElmAdd, assumption)
    apply (simp add:nsClose ring_tOp_closed npClose)
    apply (simp add:nsClose add:ring_tOp_closed npClose)
  apply (subst ag_pOp_assoc, assumption)
    apply (simp add:nsumElmClose nsClose ring_tOp_closed npClose)
    apply (simp add:nsumElmClose nsClose ring_tOp_closed npClose)
    apply (simp add:nsClose ring_tOp_closed npClose)
    apply (rule ag_pOp_closed, assumption)
    apply (simp add:ring_tOp_closed ring_r_one npClose)
    apply (simp add:agroup_def)

  apply (rule trans)
  apply (rule npMulElmL [THEN sym, of "R" "x +\<^sub>R y"], assumption)
    apply (rule ag_pOp_closed, assumption+) apply simp

  apply (rule trans) 
  apply (rule ring_distrib2 [of "R" _  "x" "y"], assumption+)
    apply (rule npClose, assumption)
    apply (rule ag_pOp_closed, assumption+)
  apply (rule gEQAddcross [THEN sym], assumption+)
    apply (rule nsumElmClose, assumption, rule allI, rule nsClose, assumption+)
      apply (rule ring_tOp_closed, assumption+, (rule npClose, assumption+)+)
    apply (rule ag_pOp_closed, assumption)
    apply (rule nsumElmClose, assumption, rule allI, rule nsClose, assumption+)
      apply (rule ring_tOp_closed, assumption+, (rule npClose, assumption+)+)
    apply (rule nsClose, assumption+, rule ring_tOp_closed, assumption+, (rule npClose, assumption+)+)
    apply (rule ring_tOp_closed, assumption+, rule npClose, assumption+, rule ag_pOp_closed, assumption+)
    apply (rule ring_tOp_closed, assumption+, rule npClose, assumption+, rule ag_pOp_closed, assumption+)

  apply simp
  apply (simp only: npeSum2_sub_muly [of "R" "x" "y"])
  apply simp

  (* final part *)
  apply simp
  apply (rule npeSum2_sub_mulx2 [THEN sym], assumption+)
  done

lemma nsumZeroFunc_sub:
  "\<And> n. \<lbrakk> ring R \<rbrakk>
	\<Longrightarrow> (\<forall> i. i \<le> n \<longrightarrow> f i = 0\<^sub>R) \<longrightarrow> (nsum0 R f n = 0\<^sub>R)";
  apply (frule ring_is_ag)
  apply (induct_tac "n")
  apply simp
  apply simp
    apply (subst ag_l_zero, assumption) apply (simp add:agroup_def)
  apply simp
  done

lemma npAdd:
  "\<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R;
     npow R x m = 0\<^sub>R; npow R y n = 0\<^sub>R \<rbrakk>
	\<Longrightarrow> npow R (x +\<^sub>R y) (m + n) = 0\<^sub>R"
  apply (subst npeSum2, assumption+)
(**
thm nsumZeroFunc_sub [THEN mp]
 **)
  apply (rule nsumZeroFunc_sub [THEN mp], assumption)
  apply (rule allI, rule impI)
  apply (rule nsZeroI, assumption) 
  apply (rule rMulZeroDiv, assumption+)
    apply (rule npClose, assumption+)
    apply (rule npClose, assumption+)

  apply (case_tac "i \<le> n")

  apply (rule disjI1)
  apply (rule npGTPowZero [of "R" "x" "m"])
    apply (assumption+)
    apply (arith)

  apply (rule disjI2)
  apply (rule npGTPowZero [of "R" "y" "n"])
    apply (assumption+)
    apply (arith)
  done

lemma npInverse:
  "\<And>n. \<lbrakk> ring R; x \<in> carrier R \<rbrakk>
	\<Longrightarrow> npow R (-\<^sub>R x) n = npow R x n 
	    \<or> npow R (-\<^sub>R x) n = -\<^sub>R (npow R x n)"
  apply (induct_tac n)
 (* n=0 *)
  apply (rule disjI1)
  apply (simp only: npow_0)

  apply (erule disjE)
 (* n:even *)
    apply (rule disjI2)
    apply (simp only:npow_suc) 
    apply (rule  ring_inv1_1 [THEN sym], assumption+)
      apply (rule npClose, assumption+)
   (* apply (rule refl) *)
 (* n:odd *)
    apply (rule disjI1)
    apply (simp only:npow_suc)  
    apply (rule ring_inv1_3 [THEN sym]) apply assumption+
    apply (simp add:npClose)
  done

lemma npMul:
  "\<And> n. \<lbrakk> ring R; x \<in> carrier R; y \<in> carrier R \<rbrakk>
	\<Longrightarrow> npow R (x \<cdot>\<^sub>R y) n = (npow R x n) \<cdot>\<^sub>R (npow R y n)"
  apply (induct_tac "n")
 (* n=0 *)
  apply simp
  apply (rule ring_r_one [THEN sym], assumption+) apply (simp add:ring_def)
 (* n>0 *)
  apply (simp only:npow_suc)
  apply (rule ring_tOp_rel, assumption+)
    apply (rule npClose, assumption+)+
  done

section "3. ring homomorphisms"

constdefs
 rHom :: "[('a, 'm) RingType_scheme, ('b, 'm1) RingType_scheme] 
                      \<Rightarrow> ('a  \<Rightarrow> 'b) set"
  "rHom A R == {f. f \<in> aHom A R \<and>
   (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f ( x \<cdot>\<^sub>A y) =  (f x) \<cdot>\<^sub>R (f y)) 
   \<and> f (1\<^sub>A) = (1\<^sub>R)}"  
constdefs
  rInvim :: "['a RingType, 'b RingType, 'a \<Rightarrow> 'b, 'b set] \<Rightarrow> 'a set"
  "rInvim A R f K == {a. a \<in> carrier A \<and> f a \<in> K}"

  rimg::"[('a, 'm) RingType_scheme, ('b, 'm1) RingType_scheme, 'a \<Rightarrow> 'b] \<Rightarrow>
            'b RingType"
  "rimg A R f == \<lparr>carrier= f `(carrier A), pOp = pOp R, mOp = mOp R,
  zero = zero R, tOp = tOp R, one = one R \<rparr>"

constdefs
 ridmap::"('a, 'm) RingType_scheme \<Rightarrow> ('a \<Rightarrow> 'a)"
 "ridmap R == \<lambda>x\<in>carrier R. x"

lemma rHom_gHom:"f \<in> rHom A R \<Longrightarrow> f \<in> aHom A R"
apply (simp add:rHom_def)
done

lemma rimg_carrier:"f \<in> rHom A R \<Longrightarrow> carrier (rimg A R f) = f ` (carrier A)"
apply (simp add:rimg_def)
done

lemma rHom_mem:"\<lbrakk> f \<in> rHom A R; a \<in> carrier A \<rbrakk> \<Longrightarrow> f a \<in> carrier R"
apply (simp add:rHom_def)
apply (frule conj_1)
 apply (thin_tac "f \<in> aHom A R \<and>
  (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f ( x \<cdot>\<^sub>A y) =  f x \<cdot>\<^sub>R (f y)) \<and> f (1\<^sub>A) = 1\<^sub>R")
 apply (simp add:aHom_def)
 apply (erule conjE)+
 apply (thin_tac " f \<in> extensional (carrier A)")
 apply (thin_tac "\<forall>x\<in>carrier A.
          \<forall>y\<in>carrier A. f ( x +\<^sub>A y) =  f x +\<^sub>R (f y)")
 apply (simp add:funcset_mem)
done

lemma ringhom1:"\<lbrakk> ring A; ring R; x \<in> carrier A; y \<in> carrier A; 
 f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (x +\<^sub>A y) = (f x) +\<^sub>R (f y)"
apply (simp add:rHom_def) apply (erule conjE)
apply (frule ring_is_ag [of "A"])
apply (frule ring_is_ag [of "R"])
apply (rule aHom_add, assumption+)
done

lemma rHom_inv_inv:"\<lbrakk> ring A; ring R; x \<in> carrier A; f \<in> rHom A R \<rbrakk> 
 \<Longrightarrow> f (-\<^sub>A x) = -\<^sub>R (f x)"
apply (frule ring_is_ag [of "A"])
apply (frule ring_is_ag [of "R"])
apply (simp add:rHom_def) apply (erule conjE)
apply (simp add:aHom_inv_inv)
done

lemma rHom_0_0:"\<lbrakk> ring A; ring R; f \<in> rHom A R \<rbrakk>  \<Longrightarrow> f (0\<^sub>A) = (0\<^sub>R)"
apply (frule ring_is_ag [of "A"])
apply (frule ring_is_ag [of "R"])
apply (simp add:rHom_def) apply (erule conjE)+
apply (simp add:aHom_0_0)
done

lemma rHom_tOp:"\<lbrakk> ring A; ring R; x \<in> carrier A; y \<in> carrier A; 
 f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (x \<cdot>\<^sub>A y) = (f x) \<cdot>\<^sub>R (f y)"
apply (simp add:rHom_def)
done  

lemma rHom_one:"\<lbrakk> ring A; ring R;f \<in> rHom A R \<rbrakk> \<Longrightarrow> f (1\<^sub>A) = (1\<^sub>R)" 
apply (simp add:rHom_def)
done

lemma rimg_ag:"\<lbrakk>ring A; ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow> agroup (rimg A R f)"
apply (frule ring_is_ag [of "A"])
apply (frule ring_is_ag [of "R"])
apply (simp add:rHom_def) apply (erule conjE)+
apply (subst agroup_def)
apply (simp add:rimg_def)
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. a = f x \<and> b = f y \<longrightarrow>
                            (\<exists>x\<in>carrier A.  a +\<^sub>R b = f x)")
 apply blast 
  apply (thin_tac "\<exists>x\<in>carrier A. a = f x")
  apply (thin_tac "\<exists>x\<in>carrier A. b = f x")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp 
 apply (subst aHom_add [THEN sym, of "A" "R" "f"], assumption+)
 apply (frule_tac x = x and y = y in ag_pOp_closed, assumption+)
 apply blast
apply (rule conjI)
 apply (rule univar_func_test)
 apply (simp add:image_def)
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "\<forall>xa\<in>carrier A. x = f xa \<longrightarrow> (\<exists>xa\<in>carrier A. -\<^sub>R x = f xa)")
 apply blast apply (thin_tac "\<exists>xa\<in>carrier A. x = f xa")
 apply (rule ballI) apply (rule impI) apply simp
 apply (subst aHom_inv_inv [THEN sym, of "A" "R" "f"], assumption+)
 apply (frule ag_mOp_closed [of "A"], assumption+)
 apply blast
apply (rule conjI)
 apply (simp add:image_def) 
 apply (frule aHom_0_0 [THEN sym, of "A" "R" "f"], assumption+)
 apply (frule ag_inc_zero [of "A"]) apply blast
apply (rule ballI)+
 apply (rule conjI)
  apply (rule ag_l_zero, assumption+)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
 apply (rule conjI)
  apply (rule ag_l_inv1, assumption+)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
 apply (rule conjI)
  apply (rule ag_pOp_assoc, assumption+)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
 apply (rule ag_pOp_commute, assumption+)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
  apply (simp add:aHom_def) apply (erule conjE)+ apply (simp add:funcset_mem)
done 

lemma rimg_ring:"\<lbrakk>ring A; ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow> ring (rimg A R f)"
apply (simp add:ring_def [of "rimg A R f"])
apply (simp add:rimg_ag)
apply (simp add:rimg_def)
apply (rule conjI)
apply (rule bivar_func_test [of "f ` carrier A" "f ` carrier A" "tOp R" "f ` carrier A"])
apply (rule ballI)+
apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. a = f x \<and> b = f y \<longrightarrow>
  (\<exists>x\<in>carrier A.  a \<cdot>\<^sub>R b = f x)")
 apply blast
  apply (thin_tac "\<exists>x\<in>carrier A. a = f x")
  apply (thin_tac "\<exists>x\<in>carrier A. b = f x")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (frule_tac x1 = x and y1 = y in  rHom_tOp [of "A" "R" _ _ "f", THEN sym]
                                                         , assumption+)
 apply simp
 apply (frule_tac x = x and y = y in ring_tOp_closed [of "A"], assumption+)
 apply blast
apply (rule conjI)
 apply (subst rHom_one [THEN sym, of "A" "R" "f"], assumption+)
 apply (simp add:image_def)
 apply (frule ring_one [of "A"]) apply blast
apply (rule ballI)+
apply (frule_tac a = x in rHom_mem [of "f" "A" "R"], assumption+)
apply (frule_tac a = y in rHom_mem [of "f" "A" "R"], assumption+)
apply (frule_tac a = z in rHom_mem [of "f" "A" "R"], assumption+) 
apply (simp add:ring_l_one)
apply (simp add:ring_distrib1)
apply (simp add:ring_tOp_assoc)
apply (simp add:ring_tOp_commute)
done

constdefs
 ideal::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> bool"
  "ideal R I == I <+ R \<and> (\<forall>r\<in>carrier R. \<forall>x\<in>I. (r \<cdot>\<^sub>R x \<in> I))"
translations
    "f\<degree>\<^sub>F\<^sub>,\<^sub>G " == "rind_hom F G f"
                                                          (* tOp \<rightarrow> pOp *) 
lemma ideal_pOp_closed:"\<lbrakk> ring R; ideal R I; x \<in> I; y \<in> I \<rbrakk> 
                                              \<Longrightarrow> x +\<^sub>R y \<in> I"
apply (subgoal_tac "I <+ R") prefer 2 apply (simp add:ideal_def)
apply (rule asubg_pOp_closed) 
 apply (simp add:ring_def)
 apply (simp add:asubgroup_def)
 apply (subgoal_tac "I \<subseteq> carrier (b_ag R)") prefer 2
  apply (simp add:asubgroup_def subgroup_def)
 apply (subgoal_tac "carrier (b_ag R) = carrier R")
  apply simp
 apply (simp add:b_ag_def)
 apply assumption+
done

lemma ideal_subset:"\<lbrakk>ring R; ideal R I; h \<in> I \<rbrakk> \<Longrightarrow> h \<in> carrier R"
apply (subgoal_tac "I \<subseteq> carrier R") apply (simp add:subsetD)
  apply (subgoal_tac "I \<subseteq> carrier (b_ag R)") prefer 2
  apply (subgoal_tac "subgroup (b_ag R) I") prefer 2 
  apply (simp add:ideal_def asubgroup_def) apply (simp add:subgroup_def)
  apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
  apply (simp add:b_ag_def)
done

lemma ideal_subset1:"\<lbrakk>ring R; ideal R I \<rbrakk> \<Longrightarrow> I \<subseteq> carrier R"
apply (rule subsetI)
apply (simp add:ideal_subset)
done

lemma ideal_ring_multiple:"\<lbrakk>ring R; ideal R I; x \<in> I; r \<in> carrier R \<rbrakk> \<Longrightarrow>
       r \<cdot>\<^sub>R x \<in> I"
apply (simp add:ideal_def)
done

lemma ideal_ring_multiple1:"\<lbrakk>ring R; ideal R I; x \<in> I; r \<in> carrier R \<rbrakk> \<Longrightarrow>
       x \<cdot>\<^sub>R r \<in> I"
apply (subgoal_tac "x \<cdot>\<^sub>R r = r \<cdot>\<^sub>R x") 
apply (simp add:ideal_ring_multiple)
apply (rule ring_tOp_commute)
apply assumption
apply (simp add:ideal_subset subsetD)
apply assumption
done

lemma ideal_inv1_closed:"\<lbrakk> ring R; ideal R I; x \<in> I \<rbrakk> \<Longrightarrow> -\<^sub>R x \<in> I"
apply (subgoal_tac "I <+ R") prefer 2 apply (simp add:ideal_def)
apply (simp add:asubgroup_def)
apply (subgoal_tac "iOp (b_ag R) x \<in> I") prefer 2 
apply (rule subg_iOp_closed [of "b_ag R" "I" "x"])
  apply (subgoal_tac "agroup R") prefer 2 apply (simp add:ring_def)
  apply (simp add:b_ag_group)
  apply assumption+
apply (subgoal_tac "iOp (b_ag R) = mOp R") prefer 2 
  apply (simp add:b_ag_def)
apply simp
done

lemma ideal_zero:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> 0\<^sub>R \<in> I"
apply (simp add:ideal_def asubgroup_def subgroup_def)
apply (subgoal_tac " GroupType.one (b_ag R) \<in> I") 
apply (subgoal_tac "GroupType.one (b_ag R) = 0\<^sub>R") apply simp
apply (simp add:b_ag_def) apply simp
done

lemma ideal_ele_sumTr1:"\<lbrakk> ring R; ideal R I; a \<in> carrier R; b \<in> carrier R;
a +\<^sub>R b \<in> I; a \<in> I \<rbrakk> \<Longrightarrow> b \<in> I"
apply (subgoal_tac "-\<^sub>R a \<in> I")
apply (subgoal_tac "-\<^sub>R a +\<^sub>R (a +\<^sub>R b) \<in> I")
apply (subgoal_tac "-\<^sub>R a +\<^sub>R (a +\<^sub>R b) = b")
 apply simp
 apply (subgoal_tac "agroup R")
 apply (subst ag_pOp_assoc [of "R" "-\<^sub>R a" "a" "b", THEN sym], assumption+)
 apply (simp add:ag_mOp_closed)+ 
 apply (simp add:ag_l_inv1)
 apply (simp add:ag_l_zero)
 apply (simp add:ring_def)
apply (simp add:ideal_pOp_closed)
apply (simp add:ideal_inv1_closed)
done

lemma ideal_ele_sumTr2:"\<lbrakk> ring R; ideal R I; a \<in> carrier R; b \<in> carrier R;
a +\<^sub>R b \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> a \<in> I"
apply (subgoal_tac "-\<^sub>R b \<in> I")
apply (subgoal_tac "a +\<^sub>R b +\<^sub>R (-\<^sub>R b) \<in> I")
apply (subgoal_tac "agroup R")
apply (frule ag_pOp_assoc [of "R" "a" "b" "-\<^sub>R b"], assumption+)
 apply (simp add:ag_mOp_closed)
 apply simp apply (subgoal_tac "b +\<^sub>R (-\<^sub>R b) = (-\<^sub>R b) +\<^sub>R b") apply simp
 apply (thin_tac "a +\<^sub>R b +\<^sub>R -\<^sub>R b =  a +\<^sub>R ( -\<^sub>R b +\<^sub>R b)")
 apply (thin_tac "b +\<^sub>R -\<^sub>R b =  -\<^sub>R b +\<^sub>R b")
 apply (frule ag_l_inv1 [of "R" "b"], assumption+)
 apply simp
 apply (frule ag_r_zero [of "R" "a"], assumption+)
 apply simp
 apply (rule ag_pOp_commute, assumption+)
  apply (simp add:ag_mOp_closed)
  apply (simp add:ring_def)
 apply (simp add:ideal_pOp_closed)
 apply (simp add:ideal_inv1_closed)
done

lemma ideal_condition:"\<lbrakk> ring R; I \<subseteq> carrier R; I \<noteq> {}; \<forall>x\<in>I. \<forall>y\<in>I. x +\<^sub>R (-\<^sub>R y) \<in> I; \<forall>r\<in>carrier R. \<forall>x\<in>I. r \<cdot>\<^sub>R x \<in> I \<rbrakk> \<Longrightarrow> ideal R I" 
apply (simp add:ideal_def)
 apply (frule ring_is_ag[of "R"])
 apply (rule asubg_test[of "R" "I"], assumption+)
done

lemma zero_ideal:"ring R \<Longrightarrow> ideal R {0\<^sub>R}"
apply (rule ideal_condition, assumption+)
apply (simp add:ring_def agroup_def)
apply simp
apply simp
apply (rule ag_r_inv1)
 apply (simp add:ring_def)
 apply (simp add:ring_def agroup_def)
apply simp
apply (rule ballI)
apply (simp add:ring_times_x_0)
done

lemma whole_ideal:"ring R \<Longrightarrow> ideal R (carrier R)"
apply (rule ideal_condition, assumption+)
 apply simp
 apply (subgoal_tac "0\<^sub>R \<in> carrier R")
 apply auto
 apply (rule ag_inc_zero)
 apply (simp add:ring_def)
apply (rule ag_pOp_closed[of "R" _])
 apply (simp add:ring_def)
 apply assumption
 apply (rule ag_mOp_closed)
 apply (simp add:ring_def)
 apply simp
apply (simp add:ring_tOp_closed)
done

lemma ideal_inc_one:"\<lbrakk>ring R; ideal R I; 1\<^sub>R \<in> I \<rbrakk> \<Longrightarrow> I = carrier R"
apply (rule equalityI)
apply (simp add:ideal_def asubgroup_def)
apply (subgoal_tac "I \<subseteq> carrier (b_ag R)")
apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
apply (simp add:b_ag_def)
apply (simp add:subgroup_def)
apply (rule subsetI) 
apply (subgoal_tac "x \<cdot>\<^sub>R 1\<^sub>R \<in> I")
apply (subgoal_tac "x \<cdot>\<^sub>R 1\<^sub>R = x") apply simp
apply (simp add:ring_r_one)
apply (simp add:ideal_ring_multiple)
done

lemma ideal_inc_unit:"\<lbrakk>ring R; ideal R I; a \<in> I; unit R a\<rbrakk> \<Longrightarrow> 1\<^sub>R \<in> I"
apply (simp add:unit_def)
apply (subgoal_tac "\<forall>y\<in>carrier R. RingType.tOp R a y = 1\<^sub>R \<longrightarrow> 1\<^sub>R \<in> I")
 apply blast apply (thin_tac "\<exists>y\<in>carrier R. RingType.tOp R a y = 1\<^sub>R")
 apply (rule ballI) apply (rule impI)
 apply (frule ideal_ring_multiple1[of "R" "I"], assumption+)
 apply simp
done

lemma ideal_inc_unit1:"\<lbrakk>ring R; a \<in> carrier R; unit R a; ideal R I; a \<in> I\<rbrakk>
                        \<Longrightarrow> I = carrier R"
apply (frule ideal_inc_unit[of "R" "I" "a"], assumption+)
apply (rule ideal_inc_one[of "R" "I"], assumption+)
done

lemma int_ideal:"\<lbrakk> ring R; ideal R I; ideal R J \<rbrakk> \<Longrightarrow> ideal R (I \<inter> J)"
apply (rule ideal_condition, assumption+)
apply (subgoal_tac "I \<subseteq> carrier R")
apply (subgoal_tac "J \<subseteq> carrier R")
 apply blast
apply (simp add:ideal_def asubgroup_def subgroup_def)
 apply (subgoal_tac "carrier (b_ag R) = carrier R")
 apply simp
 apply (simp add:b_ag_def)
apply (subgoal_tac "carrier (b_ag R) = carrier R")
 apply (simp add:ideal_def asubgroup_def subgroup_def)
 apply (simp add:b_ag_def)
 apply (frule ideal_zero, assumption+) apply (rotate_tac 2)
 apply (frule ideal_zero, assumption+) apply blast
apply (rule ballI)+
apply (subgoal_tac " x +\<^sub>R -\<^sub>R y \<in> I")
apply (subgoal_tac " x +\<^sub>R -\<^sub>R y \<in> J") apply blast
apply (rule ideal_pOp_closed, assumption+)
 apply simp apply (simp add:ideal_inv1_closed)
apply (rule ideal_pOp_closed, assumption+)
 apply simp apply (simp add:ideal_inv1_closed)
apply (rule ballI) apply (rule ballI) 
apply (subgoal_tac "r \<cdot>\<^sub>R x \<in> I")
apply (subgoal_tac "r \<cdot>\<^sub>R x \<in> J") apply simp
 apply (rule ideal_ring_multiple, assumption, assumption+) apply simp
 apply assumption
 apply (rule ideal_ring_multiple, assumption, assumption+) apply simp
 apply assumption
done

lemma sum_ideals:"\<lbrakk>ring R; ideal R I1; ideal R I2 \<rbrakk> \<Longrightarrow> ideal R (I1 \<^bold>+\<^sub>R I2)"
apply (subgoal_tac "I1 \<subseteq> carrier R")
apply (subgoal_tac "I2 \<subseteq> carrier R")
apply (simp add:ideal_def)
apply (rule conjI) 
apply (rule plus_subgs) apply (simp add:ring_def) apply simp apply simp
apply (rule ballI)+ 
apply (simp add:asettOp_def settOp_def b_ag_def) 
apply (subgoal_tac "\<forall>xa\<in>I1. \<forall>y\<in>I2.  xa +\<^sub>R y = x \<longrightarrow> (\<exists>xa\<in>I1. \<exists>y\<in>I2.  xa +\<^sub>R y =  r \<cdot>\<^sub>R x)") apply blast
  apply (thin_tac "\<exists>xa\<in>I1. \<exists>y\<in>I2.  xa +\<^sub>R y = x")
apply (rule ballI)+ apply (rule impI)
apply (subgoal_tac "x = xa +\<^sub>R y") apply (thin_tac "xa +\<^sub>R y = x") apply simp
 apply (thin_tac "x =  xa +\<^sub>R y")
apply (subgoal_tac " r \<cdot>\<^sub>R ( xa +\<^sub>R y) =  r \<cdot>\<^sub>R xa +\<^sub>R r \<cdot>\<^sub>R y") apply simp
apply blast
apply (rule ring_distrib1) apply assumption apply assumption
apply (simp add:subsetD) apply (simp add:subsetD) 
apply (rule sym) apply assumption
 apply (rule subsetI) apply (simp add:ideal_subset)
 apply (rule subsetI) apply (simp add:ideal_subset)
done

lemma sum_ideals_la1:"\<lbrakk>ring R; ideal R I1; ideal R I2 \<rbrakk> \<Longrightarrow> I1 \<subseteq> (I1 \<^bold>+\<^sub>R I2)"
apply (simp add:asettOp_def)
apply (subgoal_tac "I1 \<bullet>\<^sub>(b_ag R) I2 = I2 \<bullet>\<^sub>(b_ag R) I1")
apply simp
apply (rule NinHNTr0) apply (rule b_ag_group) apply (simp add:ring_def)
apply (simp add:ideal_def asubgroup_def)+
apply (subgoal_tac "nsubgroup (b_ag R) I2")
apply (rule subgnsubg) apply (rule b_ag_group) apply (simp add:ring_def)
apply simp apply assumption
apply (rule asubg_nsubg) apply (simp add:ring_def)
apply (simp add:asubgroup_def)
done

lemma sum_ideals_la2:"\<lbrakk>ring R; ideal R I1; ideal R I2 \<rbrakk> \<Longrightarrow> I2 \<subseteq> (I1 \<^bold>+\<^sub>R I2)"
apply (simp add:asettOp_def)
apply (rule NinHNTr0) apply (rule b_ag_group) apply (simp add:ring_def)
apply (simp add:ideal_def asubgroup_def)+
done

lemma sum_ideals_cont:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R I; 
        A \<subseteq> I; B \<subseteq> I \<rbrakk> \<Longrightarrow> A \<^bold>+\<^sub>R B \<subseteq> I"
apply (rule subsetI)
 apply (simp add:asettOp_def settOp_def)
 apply (simp add:b_ag_def)
apply (subgoal_tac "\<forall>xa\<in>A. \<forall>y\<in>B.  xa +\<^sub>R y = x \<longrightarrow> x \<in> I")
apply blast apply (thin_tac "\<exists>xa\<in>A. \<exists>y\<in>B.  xa +\<^sub>R y = x")
apply (rule ballI)+ apply (rule impI)
apply (frule sym) apply (thin_tac " xa +\<^sub>R y = x")
apply simp
apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:subsetD)+
done

constdefs
  Rxa :: "[('a, 'more) RingType_scheme, 'a ] \<Rightarrow> 'a set" (infixl "\<diamondsuit>" 130) 
  "Rxa R a == {x. \<exists>r\<in>carrier R. x = (r \<cdot>\<^sub>R a)}"

lemma principal_ideal:"\<lbrakk> ring R; a \<in> carrier R \<rbrakk> \<Longrightarrow> ideal R (R\<diamondsuit>a)"
apply (simp add:ideal_def)
apply (rule conjI)
apply (frule ring_is_ag)
apply (rule asubg_test [of "R" "R \<diamondsuit> a"], assumption+)
apply (rule subsetI)
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. x =  r \<cdot>\<^sub>R a \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. x =  r \<cdot>\<^sub>R a")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:ring_tOp_closed)
 apply (simp add:Rxa_def)
 apply (frule ring_times_0_x [of "R" "a"], assumption+)
 apply blast
apply (rule ballI)+
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. \<forall>s\<in>carrier R.  aa =  r \<cdot>\<^sub>R a \<and> b =  s \<cdot>\<^sub>R a
 \<longrightarrow> (\<exists>r\<in>carrier R.  aa +\<^sub>R -\<^sub>R b =  r \<cdot>\<^sub>R a)")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. aa =  r \<cdot>\<^sub>R a")
 apply (thin_tac "\<exists>r\<in>carrier R. b =  r \<cdot>\<^sub>R a") apply (rule ballI)+
 apply (rule impI) apply (erule conjE) apply simp
 apply (thin_tac "aa =  r \<cdot>\<^sub>R a") apply (thin_tac "b =  s \<cdot>\<^sub>R a")
 apply (frule_tac a = s in ring_inv1_1 [of "R" _ "a"], assumption+)
 apply simp apply (thin_tac "-\<^sub>R  s \<cdot>\<^sub>R a =  (-\<^sub>R s) \<cdot>\<^sub>R a")
 apply (frule_tac x = s in ag_mOp_closed [of "R"], assumption+)
 apply (frule_tac y1 = r and z1 = "-\<^sub>R s" in ring_distrib2 [THEN sym, 
                                            of "R" "a"],  assumption+)
 apply simp apply (thin_tac "r \<cdot>\<^sub>R a +\<^sub>R  (-\<^sub>R s) \<cdot>\<^sub>R a =  ( r +\<^sub>R -\<^sub>R s) \<cdot>\<^sub>R a")
 apply (frule_tac x = r and y = "-\<^sub>R s" in  ag_pOp_closed [of "R"], assumption+) 
 apply blast
apply (rule ballI)+
apply (simp add:Rxa_def) apply auto
apply (subst ring_tOp_assoc [THEN sym], assumption+)
apply (frule_tac x = r and y = ra in ring_tOp_closed [of "R"], assumption+)
apply blast
done

lemma a_in_principal:"\<lbrakk> ring R; a \<in> carrier R \<rbrakk> \<Longrightarrow> a \<in> (R\<diamondsuit>a)"
apply (simp add:Rxa_def) 
apply (frule ring_one [of "R"])
apply (subgoal_tac "a = 1\<^sub>R \<cdot>\<^sub>R a") apply blast
 apply (simp add:ring_l_one[THEN sym])
done

lemma Rxa_zero:"ring R \<Longrightarrow> R\<diamondsuit>(0\<^sub>R) = {0\<^sub>R}"
apply (rule equalityI) 
apply (rule subsetI)
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. x = RingType.tOp R r (0\<^sub>R) \<longrightarrow> x = 0\<^sub>R")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. x = RingType.tOp R r (0\<^sub>R)")
 apply (rule ballI) apply (rule impI)
 apply (simp add:ring_times_x_0)
apply (rule subsetI)
 apply simp
 apply (rule a_in_principal, assumption+)
apply (simp add:ring_zero)
done

lemma Rxa_nonzero:"\<lbrakk>ring R; a \<in> carrier R; a \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> Rxa R a \<noteq> {0\<^sub>R}"
apply (rule contrapos_pp, simp+)
 apply (frule a_in_principal[of "R" "a"], assumption+)
 apply simp
done

lemma ideal_cont_Rxa:"\<lbrakk>ring R; ideal R I; a \<in> I\<rbrakk> \<Longrightarrow> Rxa R a \<subseteq> I"
apply (rule subsetI)
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. x = r \<cdot>\<^sub>R a \<longrightarrow> x \<in> I")
 apply blast apply (rule ballI) apply (rule impI)
 apply (simp add:ideal_ring_multiple)
done

lemma id_ideal_psub_sum:"\<lbrakk> ring R; ideal R I; a\<in>carrier R; a \<notin> I \<rbrakk> \<Longrightarrow>
                            I \<subset> I \<^bold>+\<^sub>R R \<diamondsuit> a"  
apply (simp add:psubset_def) 
apply (frule principal_ideal, assumption)
apply (rule conjI)
apply (rule sum_ideals_la1, assumption+)
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "R \<diamondsuit> a \<subseteq> I \<^bold>+\<^sub>R R \<diamondsuit> a")
apply (frule a_in_principal [of "R" "a"], assumption)
apply (subgoal_tac "a \<in> I") apply simp 
apply (frule subsetD [of "R \<diamondsuit> a" "I \<^bold>+\<^sub>R R \<diamondsuit> a" "a"], assumption+)
apply simp
apply (rule sum_ideals_la2, assumption+)
done

consts
  sum_pr_ideals::"[('a, 'more) RingType_scheme, (nat \<Rightarrow> 'a), nat] \<Rightarrow> 'a set"
  (** means sum of principal ideals **)
primrec
 sum_pr0: "sum_pr_ideals R f 0 = R \<diamondsuit> (f 0)"
 sum_prn: "sum_pr_ideals R f (Suc n) = (R \<diamondsuit> (f (Suc n))) \<^bold>+\<^sub>R (sum_pr_ideals R f n)"

lemma restrictfun_Nset:"\<lbrakk>ring R; f \<in> Nset (Suc n) \<rightarrow> carrier R\<rbrakk>
          \<Longrightarrow> f \<in> Nset n \<rightarrow> carrier R" 
apply (simp add:Pi_def [of "Nset n"])
apply (rule allI) apply (rule impI)
apply (subgoal_tac "x \<in> Nset (Suc n)")
apply (simp add:funcset_mem)
apply (simp add:Nset_def)
done
                  
lemma sum_of_prideals0:"ring R \<Longrightarrow> \<forall>f. (\<forall>l\<in>Nset n. f l \<in> carrier R) \<longrightarrow> ideal R (sum_pr_ideals R f n)"  
apply (induct_tac n) 
apply (rule allI) apply (rule impI)
 apply (simp add:Nset_def) 
 apply (rule principal_ideal, assumption+)
(** case n **)
apply (rule allI) apply (rule impI)
apply (simp only:sum_prn)
apply (subgoal_tac "ideal R (sum_pr_ideals R f n)")
 apply (rule sum_ideals, assumption)
 apply (rule principal_ideal, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply (simp add:Nset_def) apply (simp add:Nset_def) apply assumption
 apply (subgoal_tac "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)")
apply blast
 apply (simp add:Nset_def)
done

lemma sum_of_prideals:"\<lbrakk>ring R; \<forall>l\<in>Nset n. f l \<in> carrier R\<rbrakk>
 \<Longrightarrow> ideal R (sum_pr_ideals R f n)" 
apply (simp add:sum_of_prideals0)
done
 
text {* later, we show sum_pr_ideals is the least ideal containing 
        {f 0, f 1,\<dots>, f n} *}

lemma sum_of_prideals1:"ring R \<Longrightarrow> \<forall>f. (\<forall>l\<in>Nset n. f l \<in> carrier R) \<longrightarrow> f ` (Nset n) \<subseteq> (sum_pr_ideals R f n)" 
apply (induct_tac n)
 apply (rule allI)
 apply (rule impI)
apply (simp add:Nset_def)
 apply (simp add:a_in_principal)

apply (rule allI) apply (rule impI)
 apply simp
 apply (subgoal_tac "f ` (Nset n \<union> {Suc n}) = f ` (Nset n) \<union> {f (Suc n)}")
 apply (frule_tac a = "f (Suc n)" in  principal_ideal [of "R" ])
 apply (simp add:Nset_def)
 apply (frule_tac  n = n and f = f in sum_of_prideals [of "R"])
 apply (simp add:Nset_def)
 apply (frule_tac  ?I1.0 = "R \<diamondsuit> f (Suc n)" and ?I2.0 = "sum_pr_ideals R f n" in sum_ideals_la1 [of "R"], assumption+)
 apply (subgoal_tac "f ` (Nset (Suc n)) = f ` (Nset n \<union> {Suc n})")
 apply simp
apply (rule conjI)
 apply (thin_tac "f ` Nset (Suc n) = insert (f (Suc n)) (f ` Nset n)")
 apply (thin_tac "R \<diamondsuit> f (Suc n) \<subseteq> R \<diamondsuit> f (Suc n) \<^bold>+\<^sub>R (sum_pr_ideals R f n)")
 apply (frule_tac a = "f (Suc n)" in a_in_principal [of "R"])
  apply (simp add:Nset_def)
 apply (frule_tac  ?I1.0 = "R \<diamondsuit> f (Suc n)" and ?I2.0 = "sum_pr_ideals R f n" in sum_ideals_la1 [of "R"], assumption+) 
 apply (rule subsetD, assumption+)
 apply (subgoal_tac "f ` Nset n \<subseteq> sum_pr_ideals R f n")
 apply (frule_tac  ?I1.0 = "R \<diamondsuit> f (Suc n)" and ?I2.0 = "sum_pr_ideals R f n" in sum_ideals_la2 [of "R"], assumption+)
 apply (rule subset_trans, assumption+)
 apply (thin_tac "R \<diamondsuit> f (Suc n) \<subseteq> R \<diamondsuit> f (Suc n) \<^bold>+\<^sub>R (sum_pr_ideals R f n)")
 apply (thin_tac "f ` Nset (Suc n) = insert (f (Suc n)) (f ` Nset n)")
 apply (subgoal_tac "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)")
 apply blast apply (simp add:Nset_def)
apply (simp add:Nset_Suc) 
apply (thin_tac "\<forall>f. (\<forall>l\<in>Nset n. f l \<in> carrier R) \<longrightarrow>
                 f ` Nset n \<subseteq> sum_pr_ideals R f n")
 apply (thin_tac "\<forall>l\<in>Nset (Suc n). f l \<in> carrier R")
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Nset_def)
 apply (rule subsetI) apply (simp add:Nset_def)
done

lemma sum_of_prideals2:"\<lbrakk>ring R; \<forall>l\<in>Nset n. f l \<in> carrier R\<rbrakk>
\<Longrightarrow>  f ` (Nset n) \<subseteq> (sum_pr_ideals R f n)" 
apply (simp add:sum_of_prideals1)
done

lemma sum_of_prideals3:"\<lbrakk>ring R; ideal R I \<rbrakk> \<Longrightarrow>
 \<forall>f. (\<forall>l\<in>Nset n. f l \<in> carrier R) \<and> (f ` (Nset n) \<subseteq> I) \<longrightarrow>
     (sum_pr_ideals R f n \<subseteq> I)" 
apply (induct_tac n)
 apply (rule allI) apply (rule impI) apply (erule conjE)
 apply (simp add:Nset_def)
 apply (frule ideal_subset, assumption+)
 apply (simp add:Rxa_def) 
 apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>r\<in>carrier R. x =  r \<cdot>\<^sub>R (f 0) \<longrightarrow> x \<in> I")
apply blast apply (thin_tac "\<exists>r\<in>carrier R. x =  r \<cdot>\<^sub>R (f 0)")
 apply (simp add:ideal_ring_multiple)
apply (rule allI) apply (rule impI)
 apply (erule conjE)
 apply (simp only:sum_prn)
apply (subgoal_tac "R \<diamondsuit> f (Suc n) \<subseteq>  I")
apply (subgoal_tac "sum_pr_ideals R f n \<subseteq> I") 
apply (rule sum_ideals_cont, assumption+)
 apply (subgoal_tac "f (Suc n) \<in> carrier R")
 apply (simp add:principal_ideal)
 apply (simp add:Nset_def)
 apply (rule sum_of_prideals, assumption+) apply (simp add:Nset_def)
 apply assumption+
 apply (subgoal_tac "\<forall>l. l \<in> Nset n \<longrightarrow> l \<in> Nset (Suc n)")
 apply blast apply (simp add:Nset_def)
apply (thin_tac "\<forall>f. (\<forall>l\<in>Nset n. f l \<in> carrier R) \<and> f ` Nset n \<subseteq> I \<longrightarrow>
                 sum_pr_ideals R f n \<subseteq> I")
 apply (subgoal_tac "f (Suc n) \<in> I")
 apply (simp add:Rxa_def) apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>r\<in>carrier R. x =  r \<cdot>\<^sub>R (f(Suc n))\<longrightarrow> x \<in> I")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. x =  r \<cdot>\<^sub>R (f (Suc n))")
 apply (rule ballI) apply (rule impI) apply simp
 apply (rule ideal_ring_multiple, assumption+)
apply (subgoal_tac "f (Suc n) \<in> f ` (Nset (Suc n))")
 apply (simp add:subsetD)
 apply (simp add:image_def)
 apply (simp add:Nset_def)
apply blast
done

lemma sum_of_prideals4:"\<lbrakk>ring R; ideal R I; \<forall>l\<in>Nset n. f l \<in> carrier R; (f ` (Nset n) \<subseteq> I)\<rbrakk> \<Longrightarrow> sum_pr_ideals R f n \<subseteq> I" 
apply (simp add:sum_of_prideals3)
done

lemma ker_ideal:"\<lbrakk> ring A; ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow> ideal A (ker\<^sub>A\<^sub>,\<^sub>R f)"
apply (rule ideal_condition, assumption+) 
apply (rule subsetI) apply (simp add:ker_def)
apply (simp add:rHom_def) apply (erule conjE)+
apply (subgoal_tac "0\<^sub>A \<in> ker\<^sub>A\<^sub>,\<^sub>R f") apply (simp add:nonempty)
 apply (simp add:ker_def)
 apply (frule ring_is_ag [of "A"])
 apply (simp add:ag_inc_zero[of "A"])
 apply (frule ring_is_ag [of "R"])
 apply (simp add:aHom_0_0)
apply (rule ballI)+
 apply (simp add:ker_def) apply (erule conjE)+
 apply (rule conjI)
 apply (frule ring_is_ag [of "A"])
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ag_mOp_closed, assumption+)
apply (frule ring_is_ag [of "A"])
apply (frule_tac x = y in ag_mOp_closed [of "A"], assumption+)
 apply (frule ring_is_ag [of "R"]) apply (simp add:rHom_def) 
 apply (erule conjE)+
 apply (simp add:aHom_add)
 apply (simp add:aHom_inv_inv)
 apply (frule ag_inc_zero [of "R"]) 
 apply (simp add:ag_r_inv1 [of "R"])
apply (rule ballI)+
 apply (simp add:ker_def)
 apply (simp add:ring_tOp_closed) apply (erule conjE)
 apply (subst rHom_tOp[of "A" "R" _ _ "f"], assumption+)
 apply simp
 apply (rule ring_times_x_0, assumption+)
 apply (simp add:rHom_mem)
done

subsection "ring of integers"

 constdefs
  Zr::"int RingType"
  "Zr == \<lparr> carrier = Zset, pOp = \<lambda>n\<in>Zset. \<lambda>m\<in>Zset. (m + n),
 mOp = \<lambda>l\<in>Zset. -l, zero = 0, tOp = \<lambda>m\<in>Zset. \<lambda>n\<in>Zset. m * n, one = 1\<rparr>"

lemma ring_of_integers:"ring Zr"
apply (simp add:ring_def)
apply (rule conjI)
prefer 2
 apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
 apply (rule ballI)+
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
 apply (simp add:zadd_zmult_distrib2)
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def zmult_assoc)
 apply (simp add:Zr_def Zset_def zmult_commute)
apply (simp add:agroup_def)
 apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+ apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
apply (rule ballI)+
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
 apply (simp add:Zr_def Zset_def)
 apply (rule conjI)
  apply (simp add:Zr_def Zset_def)
  apply (simp add:Zr_def Zset_def zadd_commute)
done

constdefs
 lev :: "int set \<Rightarrow> int"
 "lev I == Zleast {n. n \<in> I \<and> 0 < n}"
  
lemma Zr_pir_lev:"\<lbrakk>ideal Zr I; I \<noteq> {0::int}\<rbrakk> \<Longrightarrow> Rxa Zr (lev I) = I"
 apply (simp add:lev_def)
 apply (subgoal_tac "{n. n \<in> I \<and> 0 < n} \<noteq> {}")
 apply (subgoal_tac "{n. n \<in> I \<and> 0 < n} \<subseteq> Zset")
 apply (subgoal_tac "LB {n. n \<in> I \<and> 0 < n} 0")
 apply (frule_tac A = "{n. n \<in> I \<and> 0 < n}" and n = 0 in Zleast, assumption+)
 apply (erule conjE)+
 apply (rule equalityI)
 apply (rule subsetI) 
 apply (thin_tac "\<forall>x\<in>{n. n \<in> I \<and> 0 < n}. Zleast {n. n \<in> I \<and> 0 < n} \<le> x")
 apply simp apply (erule conjE) apply (thin_tac "0 < Zleast {n. n \<in> I \<and> 0 < n}") apply (thin_tac "\<exists>x. x \<in> I \<and> 0 < x")
   apply (thin_tac "{n. n \<in> I \<and> 0 < n} \<subseteq> Zset")
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r\<in>carrier Zr. x =  r \<cdot>\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n})
               \<longrightarrow> x \<in> I") apply blast
  apply (thin_tac "\<exists>r\<in>carrier Zr. x =  r \<cdot>\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n})")
  apply (rule ballI) apply (rule impI)
  apply (simp add:ideal_def)
 apply simp apply (erule conjE)+
 apply (rule subsetI) 
 apply (subgoal_tac " x =
            Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) +
            x mod Zleast {n. n \<in> I \<and> 0 < n}") prefer 2 
 apply (rule_tac a = x in zmod_zdiv_equality [of _ "Zleast {n. n \<in> I \<and> 0 < n}"])
 apply (subgoal_tac "x mod Zleast {n. n \<in> I \<and> 0 < n} = 0") 
 apply simp
 apply (subgoal_tac "Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) = (x div Zleast {n. n \<in> I \<and> 0 < n}) * Zleast {n. n \<in> I \<and> 0 < n}")
 apply simp
 apply (thin_tac "Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) = x") 
 apply (simp add:Rxa_def Zr_def Zset_def) apply blast
 apply (simp add:zmult_commute)
 apply (insert ring_of_integers)
 apply (frule_tac x = "Zleast {n. n \<in> I \<and> 0 < n}" and r = "x div Zleast {n. n \<in> I \<and> 0 < n}" in ideal_ring_multiple1 [of "Zr" "I"], assumption+)
 apply (simp add:Zr_def Zset_def)
 apply (frule_tac x = "Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})" in ideal_inv1_closed [of "Zr" "I"], assumption+)
 apply (subgoal_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>(Zr) x = -\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) + (x mod Zleast {n. n \<in> I \<and> 0 < n}))")
 prefer 2 apply simp
 apply (thin_tac "x = Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) + x mod Zleast {n. n \<in> I \<and> 0 < n}")
 apply (frule_tac x = "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n}))" and y = x in ideal_pOp_closed [of "Zr" "I"], assumption+)
 apply (thin_tac "Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n}) \<in> I")
 apply (thin_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) \<in> I")
 apply (subgoal_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>(Zr) ((Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n})) +  (x mod Zleast {n. n \<in> I \<and> 0 < n})) \<in> I")
 prefer 2 apply simp
 apply (thin_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>(Zr) x = -\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>(Zr) ((Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) + (x mod Zleast {n. n \<in> I \<and> 0 < n})))")
 apply (thin_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>(Zr) (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>Zr x  \<in> I")
 apply (subgoal_tac "-\<^sub>(Zr) (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>Zr (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>Zr ((Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) + x mod Zleast {n. n \<in> I \<and> 0 < n})) = x mod Zleast {n. n \<in> I \<and> 0 < n}") 
 apply simp
 apply (frule_tac b = "Zleast {n. n \<in> I \<and> 0 < n}" and a = x in pos_mod_conj) 
 apply (erule conjE)+
 apply (rule contrapos_pp, simp+) thm zle_imp_zless_or_eq
 apply (frule_tac n = 0 and m = "x mod Zleast {n. n \<in> I \<and> 0 < n}" in zle_imp_zless_or_eq) apply (thin_tac "0 \<le> x mod Zleast {n. n \<in> I \<and> 0 < n}")
 apply (thin_tac "I \<noteq> {0}")
 apply (frule not_sym) apply (thin_tac "x mod Zleast {n. n \<in> I \<and> 0 < n} \<noteq> 0")
 apply simp
 apply (subgoal_tac "Zleast {n. n \<in> I \<and> 0 < n} \<le> x mod Zleast {n. n \<in> I \<and> 0 < n}") prefer 2 apply blast
 apply (thin_tac "\<forall>x. x \<in> I \<and> 0 < x \<longrightarrow> Zleast {n. n \<in> I \<and> 0 < n} \<le> x")
 apply (simp add:le_def)
apply (thin_tac "ideal Zr I")
 apply (thin_tac "\<forall>x. x \<in> I \<and> 0 < x \<longrightarrow> Zleast {n. n \<in> I \<and> 0 < n} \<le> x")
 apply (thin_tac "-\<^sub>Zr (Zleast {n. n \<in> I \<and> 0 < n} \<cdot>\<^sub>Zr (x div Zleast {n. n \<in> I \<and> 0 < n})) +\<^sub>Zr ((Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) + (x mod Zleast {n. n \<in> I \<and> 0 < n})))  \<in> I")
 apply (thin_tac "ring Zr")
 apply (simp add:Zr_def Zset_def)
 apply (subgoal_tac " x =
            Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n}) +
            x mod Zleast {n. n \<in> I \<and> 0 < n}") prefer 2 
 apply (rule_tac a = x in zmod_zdiv_equality [of _ "Zleast {n. n \<in> I \<and> 0 < n}"]) 
 apply (rule_tac x = x and y = "Zleast {n. n \<in> I \<and> 0 < n} * (x div Zleast {n. n \<in> I \<and> 0 < n})" and z = "x mod Zleast {n. n \<in> I \<and> 0 < n}" in int_equation, assumption+)
 apply (simp add:LB_def) apply (rule allI) apply (rule impI)
 apply (erule conjE) apply simp
 apply (rule subsetI) apply (simp add:ideal_def) apply (erule conjE)+
 apply (simp add:asubgroup_def b_ag_def subgroup_def Zr_def)
 apply (erule conjE)+ apply (simp add:subsetD)
 apply (rule contrapos_pp, simp+)
 apply (frule ideal_zero [of "Zr" "I"], assumption+)
 apply (subgoal_tac "0 \<in> I") prefer 2 apply (simp add:Zr_def)
 apply (thin_tac "0\<^sub>Zr \<in> I")
 apply (subgoal_tac "I - {0} \<noteq> {}") prefer 2 apply blast
 apply (frule nonempty_ex [of "I - {0}"]) apply (thin_tac "I - {0} \<noteq> {}")
 apply (subgoal_tac "\<forall>n. n \<in> I - {0} \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>x. x \<in> I - {0}") apply (rule allI)
 apply (rule impI) apply simp apply (erule conjE)
 apply (subgoal_tac "n < 0 \<or> n = 0 \<or> 0 < n") 
  prefer 2 apply (rule zless_linear) apply simp 
  apply (frule_tac x = n in ideal_ring_multiple [of "Zr" "I" _ "-1"], assumption+)
  apply (simp add:Zr_def Zset_def)
  apply (subgoal_tac " -1 \<cdot>\<^sub>Zr n = - n") apply simp 
  apply (thin_tac "-1 \<cdot>\<^sub>Zr n = - n") 
  apply (subgoal_tac "\<not> 0 < (-n)") prefer 2 apply blast
  apply (thin_tac "\<forall>x. x \<in> I \<longrightarrow> \<not> 0 < x") apply (simp add:le_def)
 apply (simp add:Zr_def Zset_def)
done

lemma Zr_pir:"ideal Zr I \<Longrightarrow> \<exists>n. Rxa Zr n = I" (** principal ideal ring *)
apply (case_tac "I = {(0::int)}")
 apply (subgoal_tac "Rxa Zr 0 = I") apply blast
 apply (rule equalityI)
 apply (rule subsetI) apply (simp add:Rxa_def)
 apply (simp add:Zr_def Zset_def)
 apply (rule subsetI)
 apply (simp add:Rxa_def Zr_def Zset_def)
apply (frule Zr_pir_lev [of "I"], assumption+)
 apply blast
done

section "4. quotient rings"

lemma ar_coset_same1:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; b \<in> carrier R; 
 b +\<^sub>R (-\<^sub>R a) \<in> I \<rbrakk> \<Longrightarrow> a \<uplus>\<^sub>R I = b \<uplus>\<^sub>R I"
apply (frule ring_is_ag[of "R"])
 apply (frule b_ag_group[of "R"])
 apply (simp add:ideal_def asubgroup_def) apply (erule conjE)
 apply (frule ag_carrier_carrier[THEN sym, of "R"]) 
 apply simp
 apply (frule r_cosEq[of "b_ag R" "I" "a" "b"], assumption+)
 apply (frule agop_gop [of "R"])
 apply (frule agiop_giop[of "R"]) apply simp
 apply (simp add:ar_coset_def r_coset_def)
done

lemma ar_coset_same2:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; b \<in> carrier R; 
 a \<uplus>\<^sub>R I = b \<uplus>\<^sub>R I\<rbrakk> \<Longrightarrow>  b +\<^sub>R (-\<^sub>R a) \<in> I"
apply (insert r_cosEqVar1 [of "b_ag R" "I" "a" "b"])
apply (subgoal_tac "group (b_ag R)") apply simp apply (simp add:ideal_def
asubgroup_def) apply (subgoal_tac "carrier (b_ag R) = carrier R")
apply (subgoal_tac "a \<in> carrier (b_ag R)") apply simp
apply (subgoal_tac "b \<in> carrier (b_ag R)") apply simp
apply (frule ring_is_ag[of "R"])
apply (frule agop_gop [of "R"]) apply simp
apply (frule agiop_giop [of "R"]) apply simp
apply (simp add:ar_coset_def r_coset_def)
apply (simp add:b_ag_def) apply (simp add:b_ag_def)
apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
apply (simp add:b_ag_def)
apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
apply (frule ring_is_ag[of "R"])
apply (simp add:b_ag_group[of "R"])
apply (simp add:b_ag_def)
done

lemma ar_coset_same3:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; a \<uplus>\<^sub>R I = I\<rbrakk> \<Longrightarrow> a\<in>I"
apply (simp add:ar_coset_def) 
apply (rule r_coset_fixed [of "b_ag R" "I" "a" ])
apply (rule b_ag_group) apply (simp add:ring_def)
apply (simp add:ideal_def asubgroup_def)
apply (simp add:b_ag_def)
apply assumption
done

lemma ar_coset_same4:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; a\<in>I\<rbrakk> \<Longrightarrow> a \<uplus>\<^sub>R I = I"
apply (simp add:ar_coset_def)
apply (rule r_cosUnit1_1 [of "b_ag R" "I""a"])
apply (rule b_ag_group) apply (simp add:ring_def)
apply (simp add:ideal_def asubgroup_def)
apply assumption
done

lemma belong_ar_coset1:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; x \<in> carrier R; 
x +\<^sub>R (-\<^sub>R a) \<in> I\<rbrakk> \<Longrightarrow>  x \<in> a \<uplus>\<^sub>R I"  
apply (frule ar_coset_same1 [of "R" "I" "a" "x"], assumption+)
apply (subgoal_tac "x \<in> x \<uplus>\<^sub>R I")
 apply simp
 apply (frule ring_is_ag[of "R"])
 apply (subgoal_tac "carrier R = carrier (b_ag R)")
 apply (frule agop_gop[THEN sym, of "R"])
 apply (frule agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubgroup_def)
 
apply (rule aInR_cos [of "b_ag R" "I" "x"])
 apply (rule b_ag_group) apply (simp add:ring_def)
 apply simp
 apply assumption
 apply (simp add:b_ag_def)
done

lemma a_in_ar_coset:"\<lbrakk>ring R; ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow> a \<in> a \<uplus>\<^sub>R I"
apply (rule belong_ar_coset1, assumption+)
apply (frule ring_is_ag[of "R"])
apply (simp add:ag_r_inv1)
apply (simp add:ideal_zero)
done

lemma ar_coset_subsetD:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^sub>R I \<rbrakk> \<Longrightarrow>
                           x \<in> carrier R"
 apply (subgoal_tac "carrier R = carrier (b_ag R)")
 apply (frule ring_is_ag[of "R"])
 apply (frule agop_gop [THEN sym, of "R"])
 apply (frule agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubgroup_def)
apply (rule r_cosTr0 [of "b_ag R" "I" "a" "x"])
 apply (rule b_ag_group) apply (simp add:ring_def)
 apply simp
 apply assumption+
 apply (simp add:b_ag_def)
done

lemma ar_cos_mem:"\<lbrakk>ring R; ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                                 a \<uplus>\<^sub>R I \<in> set_r_cos (b_ag R) I"
apply (frule ring_is_ag)
 apply (simp add:set_r_cos_def ar_coset_def)
 apply (frule ag_carrier_carrier[THEN sym, of "R"]) apply simp
 apply blast
done

lemma mem_ar_coset1:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^sub>R I\<rbrakk> \<Longrightarrow>
  \<exists>h\<in>I. h +\<^sub>R a = x"
 apply (frule ring_is_ag)
 apply (frule ag_carrier_carrier[THEN sym, of "R"]) 
 apply (frule agop_gop [THEN sym, of "R"])
 apply (frule agiop_giop [THEN sym, of "R"])
 apply (simp add:ar_coset_def)
 apply (simp add:ideal_def asubgroup_def)
apply (simp add:r_coset_def)
done

lemma ar_coset_mem2:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^sub>R I\<rbrakk> \<Longrightarrow>
  \<exists>h\<in>I. x = a +\<^sub>R h"
apply (frule mem_ar_coset1 [of "R" "I" "a" "x"], assumption+)
apply (subgoal_tac "\<forall>h\<in>I. h +\<^sub>R a = x \<longrightarrow> (\<exists>h\<in>I. x = a +\<^sub>R h)")
 apply blast apply (thin_tac "\<exists>h\<in>I.  h +\<^sub>R a = x")
apply (rule ballI) apply (rule impI)
apply (frule ring_is_ag[of "R"])
 apply (frule_tac h = h in ideal_subset [of "R" "I"], assumption+)
 apply (simp add:ag_pOp_commute[of "R" _ "a"])
 apply (frule sym) apply (thin_tac " a +\<^sub>R h = x")
 apply blast
done

lemma belong_ar_coset2:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; x \<in> a \<uplus>\<^sub>R I \<rbrakk>
                 \<Longrightarrow> x +\<^sub>R (-\<^sub>R a) \<in> I"
apply (frule ring_is_ag [of "R"])
apply (frule mem_ar_coset1, assumption+)
apply auto
apply (subst ag_pOp_assoc, assumption+)
 apply (simp add:ideal_subset)
 apply assumption
 apply (rule ag_mOp_closed)
 apply (simp add:ring_def)
 apply simp
apply (subst ag_r_inv1)
 apply assumption+
apply (rule ideal_pOp_closed, assumption+)
apply (simp add:ideal_zero)
done  

text{* Following lemma is not necessary to define a quotient ring. But
it makes clear that the binary operation2 of the quotient ring is well 
defined. *}

lemma quotient_ring_tr1:"\<lbrakk> ring R; ideal R I; a1 \<in> carrier R; a2 \<in> carrier R; b1 \<in> carrier R; b2 \<in> carrier R; a1 \<uplus>\<^sub>R I = a2 \<uplus>\<^sub>R I; b1 \<uplus>\<^sub>R I = b2 \<uplus>\<^sub>R I\<rbrakk> \<Longrightarrow> (a1 \<cdot>\<^sub>R b1) \<uplus>\<^sub>R I = (a2 \<cdot>\<^sub>R b2) \<uplus>\<^sub>R I" 
apply (rule ar_coset_same1, assumption+)
 apply (simp add: ring_tOp_closed)+
apply (frule ar_coset_same2 [of "R" "I" "a1" "a2"], assumption+)
apply (frule ar_coset_same2 [of "R" "I" "b1" "b2"], assumption+) 
apply (subgoal_tac "a2 \<cdot>\<^sub>R b2 +\<^sub>R (-\<^sub>R (a1 \<cdot>\<^sub>R b1)) = (a2 \<cdot>\<^sub>R b2 +\<^sub>R (-\<^sub>R a1) \<cdot>\<^sub>R b2) 
                                             +\<^sub>R  (a1 \<cdot>\<^sub>R b2 +\<^sub>R a1 \<cdot>\<^sub>R (-\<^sub>R b1))")
 apply simp
apply (subst ring_distrib1 [of "R" "a1" "b2" "-\<^sub>R b1", THEN sym], assumption+)
 apply (rule ag_mOp_closed)
  apply (simp add:ring_def) apply assumption
apply (subst ring_distrib2 [of "R" "b2" "a2" "-\<^sub>R a1", THEN sym], assumption+)
 apply (rule ag_mOp_closed)
  apply (simp add:ring_def) apply assumption
 apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:ideal_ring_multiple1)
 apply (simp add:ideal_ring_multiple)
apply (subst pOp_assocTr43 [of "R" "a2 \<cdot>\<^sub>R b2" "(-\<^sub>R a1) \<cdot>\<^sub>R b2" "a1 \<cdot>\<^sub>R b2" 
       "a1 \<cdot>\<^sub>R (-\<^sub>R b1)"])
 apply (simp add:ring_def)
 apply (simp add:ring_tOp_closed)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ag_mOp_closed)
  apply (simp add:ring_def) apply assumption+
  apply (simp add:ring_tOp_closed)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ag_mOp_closed)
  apply (simp add:ring_def) apply assumption+
apply (subst ring_distrib2 [of "R" "b2" "-\<^sub>R a1" "a1", THEN sym], assumption+)
 apply (rule ag_mOp_closed)
  apply (simp add:ring_def) apply assumption+
apply (frule ring_is_ag)
 apply (simp add:ag_l_inv1)
 apply (simp add:ring_times_0_x)
apply (subst ag_r_zero)
 apply (simp add:ring_def)
 apply (simp add:ring_tOp_closed)
 apply (simp add: ring_inv1_2)
done

constdefs
 rcostOp :: "[('a, 'm) RingType_scheme, 'a set] 
                            \<Rightarrow> (['a set, 'a set] \<Rightarrow> 'a set)" 
    
    "rcostOp R I == \<lambda>X\<in>(set_r_cos (b_ag R) I). \<lambda>Y\<in>(set_r_cos (b_ag R) I).
                {z. \<exists> x \<in> X. \<exists> y \<in> Y. \<exists>h\<in>I. (x \<cdot>\<^sub>R y) +\<^sub>R h = z}"

lemma rcostOp:"\<lbrakk>ring R; ideal R I; a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
                    rcostOp R I (a \<uplus>\<^sub>R I) (b \<uplus>\<^sub>R I) = (a \<cdot>\<^sub>R b) \<uplus>\<^sub>R I"
apply (frule ring_is_ag)
 apply (frule ar_cos_mem[of "R" "I" "a"], assumption+)
 apply (frule ar_cos_mem[of "R" "I" "b"], assumption+) 
apply (simp add:rcostOp_def)
apply (rule equalityI)
apply (rule subsetI) apply (simp add:CollectI)
 apply (rule belong_ar_coset1, assumption+)
 apply (simp add:ring_tOp_closed)
apply (auto del:subsetI)
apply (frule ring_is_ag) 
apply (rule ag_pOp_closed, assumption+) 
 apply (rule ring_tOp_closed, assumption+)
 apply (frule ar_coset_subsetD [of "R" "I" "a"], assumption+)
 apply (frule ar_coset_subsetD [of "R" "I" "b"], assumption+)
 apply (rule ideal_subset, assumption+)
 apply (subgoal_tac "xa \<cdot>\<^sub>R y +\<^sub>R h +\<^sub>R -\<^sub>R  a \<cdot>\<^sub>R b = h +\<^sub>R  xa \<cdot>\<^sub>R y +\<^sub>R -\<^sub>R  a \<cdot>\<^sub>R b")
apply simp
apply (subst ag_pOp_assoc) apply (simp add:ring_def)
 apply (simp add:ideal_subset)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ar_coset_subsetD, assumption+)
 apply (rule ar_coset_subsetD [of "R" "I" "b" _], assumption+)
apply (rule ag_mOp_closed, assumption+)
 apply (simp add:ring_tOp_closed)
apply (rule ideal_pOp_closed, assumption+) 
apply (subst ring_distrib4, assumption+)
 apply (rule ar_coset_subsetD, assumption+)
 apply (rule ar_coset_subsetD [of "R" "I" "b" _], assumption+) 
apply (rule ideal_pOp_closed, assumption+)
apply (rule ideal_ring_multiple, assumption+)
 apply (simp add:belong_ar_coset2)
 apply (rule ar_coset_subsetD, assumption+)
apply (rule ideal_ring_multiple1, assumption+)
 apply (simp add:belong_ar_coset2)
 apply assumption+
apply (rule ag_pOp_add_r, assumption+)
 apply (rule ag_pOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
  apply (rule ar_coset_subsetD, assumption+)
  apply (rule ar_coset_subsetD [of "R" "I" "b" _], assumption+)
  apply (simp add:ideal_subset)
apply (rule ag_pOp_closed, assumption+)
 apply (simp add:ideal_subset)
 apply (rule ring_tOp_closed, assumption+)
  apply (rule ar_coset_subsetD, assumption+)
  apply (rule ar_coset_subsetD [of "R" "I" "b" _], assumption+)
apply (rule ag_mOp_closed, assumption+)
 apply (rule ring_tOp_closed, assumption+)
apply (rule ag_pOp_commute, assumption+)
 apply (rule ring_tOp_closed, assumption+)
  apply (rule ar_coset_subsetD, assumption+)
  apply (rule ar_coset_subsetD [of "R" "I" "b" _], assumption+) 
  apply (simp add:ideal_subset)

apply (rule subsetI)
apply (subgoal_tac "a \<cdot>\<^sub>R b \<in> carrier R") apply (rotate_tac -1)
apply (frule mem_ar_coset1, assumption+)
apply (subgoal_tac "\<forall>h\<in>I.  h +\<^sub>R  a \<cdot>\<^sub>R b = x \<longrightarrow> x \<in> {z. \<exists>x\<in>a \<uplus>\<^sub>R I. \<exists>y\<in>b \<uplus>\<^sub>R I. \<exists>h\<in>I.   x \<cdot>\<^sub>R y +\<^sub>R h = z}")
apply blast apply (thin_tac "\<exists>h\<in>I.  h +\<^sub>R  a \<cdot>\<^sub>R b = x")
 apply (rule ballI) apply (rule impI)
 apply (simp add:CollectI)
apply (subgoal_tac " a \<cdot>\<^sub>R b +\<^sub>R h = x") apply (thin_tac " h +\<^sub>R  a \<cdot>\<^sub>R b = x")
apply (subgoal_tac "a \<in> a \<uplus>\<^sub>R I")
apply (subgoal_tac "b \<in> b \<uplus>\<^sub>R I")
apply blast
 apply (simp add:a_in_ar_coset)+
 apply (subst ag_pOp_commute, assumption+)
 apply (simp add:ideal_subset) apply simp
apply (simp add:ring_tOp_closed) 
done

constdefs

 qring ::  "[('a, 'm) RingType_scheme, 'a set] \<Rightarrow> \<lparr> carrier :: 'a set set,
 pOp :: ['a  set, 'a set] \<Rightarrow> 'a set, mOp :: 'a set \<Rightarrow> 'a set, 
 zero :: 'a set, tOp :: ['a  set, 'a set] \<Rightarrow> 'a set, one :: 'a set \<rparr>"
 
"qring R I == \<lparr> carrier = set_r_cos (b_ag R) I, pOp = \<lambda>X. \<lambda>Y. 
 (costOp (b_ag R) I X Y), mOp = \<lambda>X. (cosiOp (b_ag R) I X), zero = I,
 tOp = \<lambda>X. \<lambda>Y. rcostOp R I X Y, one = 1\<^sub>R \<uplus>\<^sub>R I\<rparr>" 

 syntax 
  "@QRING" :: "([('a, 'more) GroupType_scheme, 'a set] => ('a set) RingType)"
              (infixl "'/'\<^sub>r" 200) 
translations
  "R /\<^sub>r I" == "qring R I"

lemma qring_ring:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> ring (qring R I)"
apply (simp add:ring_def [of "qring R I"])
apply (rule conjI)
 apply (frule ring_is_ag) apply (simp add:ideal_def) apply (erule conjE)
 apply (frule Subg_Qgroup [of "R" "I"], assumption+)
 apply (simp add:agroup_def [of "aqgrp R I"])
 apply (simp add:agroup_def [of "R /\<^sub>r I"] qring_def)
 apply (subst agroup_def) apply simp apply (simp add:aqgrp_def)
apply (rule impI) apply (rule ballI) apply (erule conjE)+
 apply blast
apply (simp add:qring_def)
(** bOp2 **)
apply (frule ring_is_ag)
apply (simp add:ideal_def) apply (erule conjE) 
 apply (frule aqgrp_carrier [of "R" "I"], assumption+)
 apply simp
apply (rule conjI)
 apply (rule bivar_func_test)
 apply (rule ballI)+
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>r\<in>carrier R. \<forall>s\<in>carrier R. a = r \<uplus>\<^sub>R I \<and> b = s \<uplus>\<^sub>R I
 \<longrightarrow> (\<exists>aa\<in>carrier R. rcostOp R I a b = aa \<uplus>\<^sub>R I)")
 apply blast 
  apply (thin_tac "\<exists>aa\<in>carrier R. a = aa \<uplus>\<^sub>R I")
  apply (thin_tac "\<exists>a\<in>carrier R. b = a \<uplus>\<^sub>R I")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
apply (subst rcostOp, assumption+)
 apply (simp add:ideal_def) apply assumption+
 apply (frule_tac x = r and y = s in ring_tOp_closed [of "R"], assumption+)
 apply blast
apply (rule conjI)
 apply (frule ring_one) apply (simp add:set_ar_cos_def) apply blast
apply (rule ballI)+
 apply (thin_tac "set_r_cos (b_ag R) I = set_ar_cos R I")
apply (rule conjI)
 apply (thin_tac "y \<in> set_ar_cos R I")
 apply (thin_tac "z \<in> set_ar_cos R I")
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier R. x = a \<uplus>\<^sub>R I \<longrightarrow>
           rcostOp R I (1\<^sub>R \<uplus>\<^sub>R I) x = x") apply blast
 apply (rule ballI) apply (rule impI) apply simp
 apply (subst rcostOp, assumption+)
 apply (simp add:ideal_def) apply (simp add: ring_one) apply assumption
 apply (simp add:ring_l_one)
apply (simp add:set_ar_cos_def)
apply (rule conjI)
apply (auto del:equalityI)
prefer 3
 apply (subst rcostOp, assumption+) apply (simp add:ideal_def) 
 apply assumption+
 apply (subst rcostOp, assumption+) apply (simp add:ideal_def) 
 apply assumption+
 apply (simp add:ring_tOp_commute)
apply (subgoal_tac "ideal R I")
 apply (subst rcostOp, assumption+)+
apply (frule_tac a = aa and b = ab in aqgrp_pOp_maps [of "R" "I"], 
                                                            assumption+)  
 apply (simp add:aqgrp_def)
apply (frule_tac a = "a \<cdot>\<^sub>R aa" and b = "a \<cdot>\<^sub>R ab" in 
                         aqgrp_pOp_maps [of "R" "I"], assumption+)  
 apply (simp add:ring_tOp_closed)
 apply (simp add:ring_tOp_closed)
 apply (simp add:aqgrp_def)
apply (frule_tac x = aa and y = ab in ag_pOp_closed, assumption+)
 apply (subst rcostOp, assumption+)
 apply (simp add:ring_distrib1) apply (simp add:ideal_def)
apply (subgoal_tac "ideal R I")
 apply (subst rcostOp, assumption+)+
 apply (simp add:ring_tOp_closed)
 apply (subst rcostOp, assumption+)+
 apply (simp add:ring_tOp_closed)
 apply assumption
 apply (simp add:ring_tOp_assoc)
apply (simp add:ideal_def)
done

lemma qring_carrier:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> carrier (qring R I)
 = {X. \<exists>a\<in> carrier R. a \<uplus>\<^sub>R I = X}" 
apply (simp add:qring_def) apply (simp add:set_r_cos_def)
apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
apply (subgoal_tac "\<forall>a\<in> carrier R. r_coset (b_ag R) I a = a \<uplus>\<^sub>R I") 
apply simp apply blast
apply (simp add:ar_coset_def)
apply (simp add:b_ag_def)
done

lemma qring_mem:"\<lbrakk> ring R; ideal R I; a \<in> carrier R \<rbrakk> \<Longrightarrow> 
                                 a \<uplus>\<^sub>R I \<in>  carrier (qring R I)" 
apply (simp add:qring_carrier)
apply blast
done

lemma qring_pOp:"\<lbrakk> ring R; ideal R I; a \<in> carrier R; b \<in> carrier R \<rbrakk>
 \<Longrightarrow> pOp (qring R I) (a \<uplus>\<^sub>R I) (b \<uplus>\<^sub>R I) = (a +\<^sub>R b) \<uplus>\<^sub>R I"
apply (simp add:qring_def)
apply (frule ring_is_ag[of "R"])
apply (subgoal_tac "costOp (b_ag R) I (r_coset (b_ag R) I a) 
 (r_coset (b_ag R) I b) = r_coset (b_ag R) I (GroupType.tOp (b_ag R) a b)") 
prefer 2 apply (rule costOpwelldef [THEN sym])
 apply (rule b_ag_group) apply (simp add:ring_def)
 apply (rule asubg_nsubg) apply (simp add:ring_def)
 apply (simp add:ideal_def) apply (simp add:b_ag_def)
 apply (simp add:b_ag_def)
apply (frule agop_gop[of "R"])
apply simp
apply (simp add:ar_coset_def)
done

lemma qring_zero:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> zero (qring R I) = I"
apply (simp add:qring_def)
done

lemma qring_zero_1:"\<lbrakk> ring R; a\<in>carrier R; ideal R I; a \<uplus>\<^sub>R I = I\<rbrakk> \<Longrightarrow> a \<in> I"
apply (frule a_in_ar_coset [of "R" "I" "a"], assumption+) apply simp
done

lemma Qring_fix1:"\<lbrakk> ring R; a\<in>carrier R; ideal R I; a \<in> I\<rbrakk> \<Longrightarrow> a \<uplus>\<^sub>R I = I"
apply (simp add:ar_coset_def) 
apply (frule ring_is_ag)
apply (frule b_ag_group)
apply (simp add:ideal_def) apply (erule conjE) apply (simp add:asubgroup_def)
apply (rule  r_cosUnit1_1 [of "b_ag R" "I" "a"], assumption+)
done

lemma ar_cos_same:"\<lbrakk>ring R; a\<in>carrier R; ideal R I; x \<in> a \<uplus>\<^sub>R I\<rbrakk> \<Longrightarrow>
                    x \<uplus>\<^sub>R I = a \<uplus>\<^sub>R I" 
apply (subst ar_coset_def)+
apply (frule ring_is_ag)
apply (frule b_ag_group)
apply (simp add:ideal_def) apply (erule conjE) apply (simp add:asubgroup_def)
apply (rule r_cosEqVar2 [THEN sym, of "b_ag R" "I" "a" "x"], assumption+)
apply (simp add:ag_carrier_carrier)
apply (simp add:ar_coset_def)
done

lemma qring_tOp:"\<lbrakk> ring R; ideal R I; a \<in> carrier R; b \<in> carrier R \<rbrakk>
 \<Longrightarrow> tOp (qring R I) (a \<uplus>\<^sub>R I) (b \<uplus>\<^sub>R I) = (a \<cdot>\<^sub>R b) \<uplus>\<^sub>R I"
apply (simp add:qring_def)
apply (simp add:rcostOp)  
done

lemma rind_hom_well_def:"\<lbrakk> ring A; ring R; f \<in> rHom A R; a \<in> carrier A \<rbrakk> \<Longrightarrow>
                                   f a = (f\<degree>\<^sub>A\<^sub>,\<^sub>R) (a \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f))"
apply (subgoal_tac "(a \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f)) \<in> set_ar_cos A (ker\<^sub>A\<^sub>,\<^sub>R f)")  
apply (simp add:rind_hom_def)
 apply (subgoal_tac "\<exists>x. x \<in> a \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f)")
 apply (rule someI2_ex, assumption+)
apply (thin_tac "\<exists>x. x \<in> a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (subgoal_tac "ideal A (ker\<^sub>A\<^sub>,\<^sub>R f)")
 apply (frule mem_ar_coset1, assumption+)
apply (subgoal_tac "\<forall>h\<in>ker\<^sub>A\<^sub>,\<^sub>R f.  h +\<^sub>A a = x \<longrightarrow> f a = f x")
 apply blast apply (thin_tac "\<exists>h\<in>ker\<^sub>A\<^sub>,\<^sub>R f.  h +\<^sub>A a = x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "x = h +\<^sub>A a") apply (thin_tac " h +\<^sub>A a = x")
 apply simp
apply (subgoal_tac "f ( h +\<^sub>A a) = (f h) +\<^sub>R (f a)")
 apply simp
 apply (simp add:ker_def)
 apply (subst ag_l_zero) apply (simp add:ring_is_ag[of "R"])
  apply (simp add:rHom_mem)
  apply simp
 apply (rule ringhom1, assumption+)
 apply (simp add:ideal_subset)
 apply assumption+
 apply (rule sym, assumption+)
apply (simp add:ker_ideal)
apply (subgoal_tac "a \<in> a \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f)")
apply blast
apply (rule a_in_ar_coset, assumption+)
 apply (simp add:ker_ideal)
 apply assumption
apply (simp add:set_ar_cos_def)
apply blast
done

lemma set_r_ar_cos:"\<lbrakk>ring A; ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow>
  set_r_cos (b_ag A) (ker\<^sub>A\<^sub>,\<^sub>R f) = set_ar_cos A (ker\<^sub>A\<^sub>,\<^sub>R f)"
apply (simp add:set_r_cos_def set_ar_cos_def)
 apply (simp add:ar_coset_def)
 apply (subgoal_tac "carrier (b_ag A) = carrier A") apply simp
 apply (simp add:b_ag_def)
done

lemma ind_hom_rhom:"\<lbrakk> ring A; ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                     (f\<degree>\<^sub>A\<^sub>,\<^sub>R) \<in> rHom (qring A (ker\<^sub>A\<^sub>,\<^sub>R f)) R"
apply (simp add:rHom_def [of "qring A (ker\<^sub>A\<^sub>,\<^sub>R f)" "R"])
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (simp add:qring_def)
apply (simp add:rind_hom_def extensional_def)
apply (rule univar_func_test)
 apply (rule ballI)
 apply (frule ring_is_ag [of "A"])
 apply (frule ring_is_ag [of "R"])
 apply (frule b_ag_group [of "R"])
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:set_ar_cos_def)
 apply (rule conjI)
 apply (rule impI)
 apply (subgoal_tac "\<forall>a\<in>carrier A. x = a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f \<longrightarrow>
                       f (SOME xa. xa \<in> x) \<in> carrier (b_ag R)")
 apply blast apply (thin_tac "\<exists>a\<in>carrier A. x = a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (rule ballI) apply (rule impI)
 apply (frule ker_ideal [of "A" "R" "f"], assumption+)
 apply (frule_tac a = a in a_in_ar_coset [of "A" "ker\<^sub>A\<^sub>,\<^sub>R f"], assumption+)
 apply simp
 apply (rule someI2_ex) apply blast 
 apply (frule_tac a = a and x = xa in ar_coset_subsetD [of "A" "ker\<^sub>A\<^sub>,\<^sub>R f"], 
                                                         assumption+)
 apply (subst ag_carrier_carrier, assumption+)
 apply (simp add:rHom_mem)
 apply (rule impI)
 apply (simp add:set_r_ar_cos)
 apply (simp add:set_ar_cos_def)
apply (rule conjI)
 apply (simp add:qring_def)
 apply (simp add:set_r_ar_cos)
 apply (simp add:rind_hom_def extensional_def)
apply (rule ballI)+
 apply (simp add:qring_def)
 apply (simp add:set_r_ar_cos)
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>s\<in>carrier A. \<forall>t\<in>carrier A. a = s \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f \<and> 
  b = t \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f \<longrightarrow> ((f\<degree>\<^sub>A\<^sub>,\<^sub>R) (costOp (b_ag A) (ker\<^sub>A\<^sub>,\<^sub>R f) a b) =
              (f\<degree>\<^sub>A\<^sub>,\<^sub>R) a +\<^sub>R ((f\<degree>\<^sub>A\<^sub>,\<^sub>R) b))")  
 apply blast apply (thin_tac "\<exists>aa\<in>carrier A. a = aa \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (thin_tac "\<exists>a\<in>carrier A. b = a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (rule ballI)+
 apply (rule impI) apply (erule conjE) apply simp
 apply (frule ker_ideal [of "A" "R" "f"], assumption+)
 apply (frule ring_is_ag [of "A"])
 apply (simp add:ideal_def) apply (erule conjE)+
 apply (frule_tac a = s and b = t in aqgrp_pOp_maps [of "A" "ker\<^sub>A\<^sub>,\<^sub>R f"],
                                                       assumption+)
 apply (simp add:aqgrp_def)
 apply (frule_tac x = s and y = t in ag_pOp_closed [of "A"], assumption+)
 apply (simp add:rind_hom_well_def[THEN sym])
 apply (simp add:rHom_def) apply (erule conjE)+
 apply (frule ring_is_ag [of "R"])
 apply (simp add:aHom_add)
apply (rule conjI)
apply (rule ballI)+
 apply (simp add:qring_def) apply (simp add:set_r_ar_cos) 
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>s\<in>carrier A. \<forall>t\<in>carrier A.  x = s \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f \<and>
  y = t \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f \<longrightarrow> (f\<degree>\<^sub>A\<^sub>,\<^sub>R) (rcostOp A (ker\<^sub>A\<^sub>,\<^sub>R f) x y) =  (f\<degree>\<^sub>A\<^sub>,\<^sub>R) x \<cdot>\<^sub>R ((f\<degree>\<^sub>A\<^sub>,\<^sub>R) y)")   
 apply blast apply (thin_tac "\<exists>a\<in>carrier A. x = a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
             apply (thin_tac "\<exists>a\<in>carrier A. y = a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (rule ballI)+ apply (rule impI) apply (erule conjE) apply simp
 apply (frule ker_ideal [of "A" "R" "f"], assumption+)
 apply (subst rcostOp, assumption+)
 apply (frule_tac x = s and y = t in ring_tOp_closed, assumption+)
 apply (simp add:rind_hom_well_def[THEN sym])
 apply (simp add:rHom_tOp)
apply (simp add:qring_def)
 apply (frule ring_one [of "A"])
 apply (simp add:rind_hom_well_def [THEN sym])
 apply (simp add:rHom_one)
done

lemma ind_hom_injec:"\<lbrakk>ring A; ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow> 
                              injec\<^sub>(qring A (ker\<^sub>A\<^sub>,\<^sub>R f))\<^sub>,\<^sub>R (f\<degree>\<^sub>A\<^sub>,\<^sub>R)"
apply (simp add:injec_def)
apply (frule ind_hom_rhom [of "A" "R" "f"], assumption+)
apply (simp add:rHom_def)
apply (simp add:qring_def)
apply (frule set_r_ar_cos [of "A" "R" "f"], assumption+) apply (fold qring_def)
apply (simp add:rHom_def) apply simp
 apply (thin_tac " set_r_cos (b_ag A) (ker\<^sub>A\<^sub>,\<^sub>R f) = set_ar_cos A (ker\<^sub>A\<^sub>,\<^sub>R f)")
 apply (erule conjE)+ 
 apply (simp add:ker_def [of _ _ "f\<degree>\<^sub>A\<^sub>,\<^sub>R"])
 apply (subst qring_carrier, assumption+) 
 apply (rule ker_ideal, assumption+) apply (simp add:rHom_def)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (erule conjE)+
 apply (subgoal_tac "\<forall>a\<in>carrier A. a \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f) = x \<longrightarrow>
                      x = ker\<^sub>A\<^sub>,\<^sub>R f") apply blast
 apply (thin_tac "\<exists>a\<in>carrier A. a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f = x")
 apply (rule ballI) apply (rule impI) apply (rotate_tac -1)
 apply (frule sym) apply (thin_tac "a \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f = x") apply simp
 apply (subgoal_tac "f \<in> rHom A R") prefer 2 apply (simp add:rHom_def)
 apply (simp add:rind_hom_well_def [THEN sym])
 apply (subgoal_tac "a \<in> ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (subst Qring_fix1, assumption+)
 apply (rule  ker_ideal, assumption+) apply simp
 apply (simp add:ker_def)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (frule ring_zero[of "A"]) 
 apply (subgoal_tac "0\<^sub>A \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f = ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (rule conjI) apply blast apply (rotate_tac -1) apply (frule sym)
 apply (thin_tac "0\<^sub>A \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f = ker\<^sub>A\<^sub>,\<^sub>R f") 
 apply (subgoal_tac "(f\<degree>\<^sub>A\<^sub>,\<^sub>R) (ker\<^sub>A\<^sub>,\<^sub>R f) = (f\<degree>\<^sub>A\<^sub>,\<^sub>R) (0\<^sub>A \<uplus>\<^sub>A ker\<^sub>A\<^sub>,\<^sub>R f)") 
 apply (frule rind_hom_well_def [THEN sym, of "A" "R" "f" "0\<^sub>A"], assumption+)
 apply (simp add:rHom_def) apply (simp add:ring_one)
 apply simp apply (rule rHom_0_0, assumption+) apply (simp add:rHom_def)
 apply simp
 apply (rule Qring_fix1, assumption+)
  apply (rule  ker_ideal, assumption+) apply (simp add:rHom_def)
 apply (simp add:ker_def)
 apply (rule rHom_0_0, assumption+) apply (simp add:rHom_def)
done

lemma rhom_to_rimg:"\<lbrakk>ring A; ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
                                   f \<in> rHom A (rimg A R f)"
apply (subgoal_tac "\<forall>z. z\<in> f `(carrier A) \<longrightarrow> z \<in> carrier R") 
 apply (simp add:rHom_def aHom_def)
apply (rule conjI)
 apply (erule conjE)+
 apply (simp add:rimg_def)
 apply (rule univar_func_test)
 apply (rule ballI) apply (simp add:image_def)
 apply blast
apply (simp add:rimg_def)
apply (rule allI)
 apply (rule impI)
 apply (simp add:image_def)
 apply auto
 apply (simp add:rHom_mem)
done

lemma ker_to_rimg:"\<lbrakk>ring A; ring R; f \<in> rHom A R \<rbrakk> \<Longrightarrow>
                         ker\<^sub>A\<^sub>,\<^sub>R f = ker\<^sub>A\<^sub>,\<^sub>(rimg A R f) f"
apply (frule rhom_to_rimg [of "A" "R" "f"], assumption+)
apply (simp add:ker_def)
apply (simp add:rimg_def)
done

lemma indhom_bijec2_rimg:"\<lbrakk>ring A; ring R; f \<in> rHom A R\<rbrakk> \<Longrightarrow>
     bijec\<^sub>(qring A (ker\<^sub>A\<^sub>,\<^sub>R f))\<^sub>,\<^sub>(rimg A R f) (f\<degree>\<^sub>A\<^sub>,\<^sub>R)"
apply (frule rimg_ring [of "A" "R" "f"], assumption+)
apply (frule rhom_to_rimg[of "A" "R" "f"], assumption+)
apply (frule ind_hom_rhom[of "A" "rimg A R f" "f"], assumption+)
 apply (subgoal_tac "ker\<^sub>A\<^sub>,\<^sub>(rimg A R f) f = ker\<^sub>A\<^sub>,\<^sub>R f")
 apply (subgoal_tac "f\<degree>\<^sub>A\<^sub>,\<^sub>(rimg A R f) = f\<degree>\<^sub>A\<^sub>,\<^sub>R")
 apply simp
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:injec_def)
 apply (rule conjI) apply (simp add:rHom_def)
 apply (frule ind_hom_injec [of "A" "R" "f"], assumption+)
 apply (simp add:injec_def)
 apply (simp add:ker_def [of _ _ "f\<degree>\<^sub>A\<^sub>,\<^sub>R"]) apply (simp add:rimg_def)
apply (simp add:surjec_def) 
 apply (rule conjI) apply (simp add:rHom_def)
 apply (rule surj_to_test)
 apply (simp add:rHom_def aHom_def)
apply (rule ballI)
 apply (subgoal_tac "carrier (rimg A R f) = f `(carrier A)")
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>x\<in>carrier A. b = f x \<longrightarrow> (\<exists>a\<in>carrier (qring A (ker\<^sub>A\<^sub>,\<^sub>R f)). (f\<degree>\<^sub>A\<^sub>,\<^sub>R) a = b)")
 apply blast apply (thin_tac "\<exists>x\<in>carrier A. b = f x")
 apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "(f\<degree>\<^sub>A\<^sub>,\<^sub>R) (x \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f)) = b")
 apply (subgoal_tac "(x \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f))\<in> carrier (qring A (ker\<^sub>A\<^sub>,\<^sub>R f))")
 apply blast
  apply (thin_tac "f\<degree>\<^sub>A\<^sub>,\<^sub>R \<in> rHom (qring A (ker\<^sub>A\<^sub>,\<^sub>R f)) (rimg A R f)")
 apply (simp add:qring_def)
 apply (simp add:set_r_ar_cos)
 apply (simp add:set_ar_cos_def) apply blast apply simp
 apply (simp add: rind_hom_well_def [of "A" "R" "f" _])
apply (simp add:rimg_def)
apply (frule  ind_hom_injec[of "A" "R" "f"], assumption+)
apply (simp add:injec_def)
 apply (subgoal_tac "\<forall>x. (f\<degree>\<^sub>A\<^sub>,\<^sub>(rimg A R f)) x  = (f\<degree>\<^sub>A\<^sub>,\<^sub>R) x")
 apply (simp add:expand_fun_eq)
 apply (rule allI)
 apply (simp add:rind_hom_def)
apply (simp add:ker_to_rimg [THEN sym])
done

lemma surjec_ind_bijec:"\<lbrakk>ring A; ring R; f \<in> rHom A R; surjec\<^sub>A\<^sub>,\<^sub>R f\<rbrakk> \<Longrightarrow>
     bijec\<^sub>(qring A (ker\<^sub>A\<^sub>,\<^sub>R f))\<^sub>,\<^sub>R (f\<degree>\<^sub>A\<^sub>,\<^sub>R)"
apply (frule ind_hom_rhom[of "A" "R" "f"], assumption+)
apply (simp add:surjec_def)
apply (simp add:bijec_def)
apply (rule conjI)
 apply (simp add:injec_def) apply (erule conjE)+ 
 apply (simp add:rHom_def)
 apply (frule ind_hom_injec [of "A" "R" "f"], assumption+)
 apply (simp add:rHom_def) apply (simp add:injec_def)
apply (simp add:surjec_def) 
 apply (rule conjI)
 apply (simp add:rHom_def)
 apply (rule surj_to_test [of "(f\<degree>\<^sub>A\<^sub>,\<^sub>R)" "carrier (qring A (ker\<^sub>A\<^sub>,\<^sub>R f))" "carrier R"])
 apply (thin_tac "f \<in> aHom A R \<and> surj_to f (carrier A) (carrier R)")
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:rHom_mem)
apply (rule ballI)
 apply (erule conjE)
 apply (simp add:surj_to_def image_def)
 apply (subgoal_tac "b \<in> {y. \<exists>x\<in>carrier A. y = f x}")
  apply (thin_tac "{y. \<exists>x\<in>carrier A. y = f x} = carrier R")
 apply (simp add:CollectI)
apply auto  
 apply (subgoal_tac "(f\<degree>\<^sub>A\<^sub>,\<^sub>R) (x \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f)) = f x")
 apply (subgoal_tac "(x \<uplus>\<^sub>A (ker\<^sub>A\<^sub>,\<^sub>R f))\<in> carrier (qring A (ker\<^sub>A\<^sub>,\<^sub>R f))") 
 apply blast
apply (simp add:qring_def) apply (fold qring_def)
 apply (simp add:set_r_ar_cos)
 apply (simp add:set_ar_cos_def) apply blast
 apply (simp add: rind_hom_well_def [of "A" "R" "f" _])
done

lemma ridmap_ind_bijec:"ring A \<Longrightarrow>
     bijec\<^sub>(qring A (ker\<^sub>A\<^sub>,\<^sub>A (ridmap A)))\<^sub>,\<^sub>A ((ridmap A)\<degree>\<^sub>A\<^sub>,\<^sub>A)"
apply (subgoal_tac "surjec\<^sub>A\<^sub>,\<^sub>A (ridmap A)")
apply (rule surjec_ind_bijec [of "A" "A" "ridmap A"], assumption+)
 apply (simp add:rHom_def) 
 apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI) apply (rule  univar_func_test) apply (rule ballI)
 apply (simp add:ridmap_def)
 apply (rule conjI)
 apply (simp add:ridmap_def extensional_def)
apply (rule ballI)+
 apply (simp add:ridmap_def) apply (frule ring_is_ag)
 apply (simp add:ag_pOp_closed)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:ridmap_def) apply (simp add:ring_tOp_closed)
apply (simp add:ridmap_def) apply (simp add:ring_one)
 apply assumption
 apply (simp add:surjec_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (simp add:Pi_def ridmap_def)
 apply (rule ballI)+ apply (frule ring_is_ag) apply (simp add:ag_pOp_closed)
apply (rule surj_to_test) 
 apply (rule univar_func_test) 
 apply (rule ballI) apply (simp add:ridmap_def)
 apply (rule ballI) apply (simp add:ridmap_def)
done

lemma ker_of_idmap:"ring A \<Longrightarrow> ker\<^sub>A\<^sub>,\<^sub>A (ridmap A) = {0\<^sub>A}" 
apply (simp add:ker_def)
apply (simp add:ridmap_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (rule subsetI) apply (simp add:CollectI)
apply (frule ring_is_ag)
 apply (simp add:ag_inc_zero)
done

lemma ring_natural_isom:"ring A \<Longrightarrow> bijec\<^sub>(qring A {0\<^sub>A})\<^sub>,\<^sub>A ((ridmap A)\<degree>\<^sub>A\<^sub>,\<^sub>A)"
apply (frule ridmap_ind_bijec)
apply (simp add: ker_of_idmap)
done           (** A /\<^sub>r {0\<^sub>A}\<^sub> \<cong> A **)

constdefs
 pj :: "['a RingType, 'a set] \<Rightarrow>  ( 'a => 'a set)" 
      "pj R I == \<lambda>x. Pj (b_ag R) I x" 

 (* pj is projection homomorphism *)

lemma pj_Hom:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> (pj R I) \<in> rHom R (qring R I)"
apply (simp add:rHom_def)
apply (rule conjI) 
apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply (simp add:qring_def)
 apply (frule ring_is_ag)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:set_r_cos_def) apply blast
apply (rule conjI)
 apply (simp add:pj_def Pj_def extensional_def) 
 apply (frule ring_is_ag) apply (simp add:ag_carrier_carrier)
apply (rule ballI)+
 apply (frule ring_is_ag)
 apply (frule_tac x = a and y = b in ag_pOp_closed, assumption+)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:qring_def) apply (frule b_ag_group)
 apply (simp add:agop_gop [THEN sym])
 apply (rule costOpwelldef, assumption+) apply (simp add:ideal_def)
 apply (erule conjE) apply (simp add:asubg_nsubg) apply assumption+
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add: qring_def)
 apply (frule_tac x = x and y = y in ring_tOp_closed, assumption+)
 apply (frule ring_is_ag) apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:ag_carrier_carrier)
 apply (frule_tac a1 = x and b1 = y in rcostOp [THEN sym, of "R" "I"], 
                                                             assumption+)
 apply (simp add:ar_coset_def)
apply (simp add:qring_def)
 apply (frule ring_one)
 apply (frule ring_is_ag) apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:pj_def Pj_def)
 apply (simp add:ar_coset_def)
done

lemma pj_mem:"\<lbrakk> ring R; ideal R I; x \<in> carrier R\<rbrakk> \<Longrightarrow> pj R I x = x \<uplus>\<^sub>R I"
apply (frule ring_is_ag) apply (simp add:ag_carrier_carrier [THEN sym])
apply (simp add:pj_def Pj_def)
apply (simp add:ar_coset_def)
done

lemma invim_of_ideal:"\<lbrakk>ring R; ideal R I; ideal (qring R I) J \<rbrakk> \<Longrightarrow> 
  ideal R (rInvim R (qring R I) (pj R I) J)"
apply (rule ideal_condition, assumption)
 apply (simp add:rInvim_def) apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "0\<^sub>R \<in> rInvim R (qring R I) (pj R I) J")
apply (simp add:nonempty)
apply (simp add:rInvim_def)
apply (simp add: ring_zero)
 apply (frule ring_is_ag)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (frule qring_ring [of "R" "I"], assumption+)
 apply (frule rHom_0_0 [of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:ideal_zero)
apply (rule ballI)+
 apply (simp add:rInvim_def) apply (erule conjE)+
 apply (rule conjI)
 apply (frule ring_is_ag)
 apply (rule ag_pOp_closed, assumption+) 
 apply (rule ag_mOp_closed, assumption+)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (frule ring_is_ag)
 apply (frule_tac x = y in ag_mOp_closed [of "R"], assumption+)
 apply (simp add:rHom_def) apply (erule conjE)+
 apply (subst aHom_add [of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:qring_ring ring_is_ag)
 apply assumption+
apply (frule qring_ring [of "R" "I"], assumption+)
 apply (rule ideal_pOp_closed, assumption+)
 apply (subst aHom_inv_inv[of "R" "R /\<^sub>r I" "pj R I"], assumption+)
 apply (simp add:ring_is_ag) apply assumption+
 apply (frule_tac x = "pj R I y" in ideal_inv1_closed [of "R /\<^sub>r I" "J"],
                                              assumption+)
apply (rule ballI)+
 apply (simp add:rInvim_def) apply (erule conjE)
 apply (simp add:ring_tOp_closed)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (subst rHom_tOp [of "R" "R /\<^sub>r I" _ _ "pj R I"], assumption+)
 apply (frule qring_ring[of "R" "I"], assumption+) 
 apply (rule ideal_ring_multiple [of "R /\<^sub>r I" "J"])
 apply (simp add:qring_ring) apply assumption+
 apply (simp add:rHom_mem)
done

lemma pj_invim_cont_I:"\<lbrakk> ring R; ideal R I; ideal (qring R I) J \<rbrakk> \<Longrightarrow> 
          I \<subseteq> (rInvim R (qring R I) (pj R I) J)"
apply (rule subsetI)
 apply (simp add:rInvim_def)
 apply (frule ideal_subset [of "R" "I"], assumption+)
 apply simp
 apply (frule  pj_mem [of "R" "I"  _], assumption+)
 apply (simp add:ar_coset_same4)
apply (subgoal_tac "ring (qring R I)")
apply (frule ideal_zero [of "qring R I" "J"], assumption+)
apply (subgoal_tac "0\<^sub>qring R I = I") apply simp
 apply (thin_tac "0\<^sub>qring R I \<in> J")
 apply (simp add:qring_def agroup_def)
 apply (simp add:qring_ring)
done

lemma pj_invim_mono1:"\<lbrakk> ring R; ideal R I; ideal (qring R I) J1; ideal (qring R I) J2; J1 \<subseteq> J2 \<rbrakk> \<Longrightarrow> (rInvim R (qring R I) (pj R I) J1) \<subseteq> (rInvim R (qring R I) (pj R I) J2)"
apply (rule subsetI) 
apply (simp add:rInvim_def)
apply (simp add:subsetD)
done

lemma pj_img_ideal:"\<lbrakk> ring R; ideal R I; ideal R J; I \<subseteq> J \<rbrakk> \<Longrightarrow> 
                                     ideal (qring R I) ((pj R I)`J)"
apply (rule ideal_condition [of "qring R I" "(pj R I) `J"]) 
apply (simp add:qring_ring)
apply (rule subsetI) apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>J. x = (pj R I) xa \<longrightarrow> x \<in> carrier (qring R I)")
 apply blast apply (thin_tac "\<exists>xa\<in>J. x = pj R I xa")
 apply (rule ballI) apply (rule impI) apply simp
 apply (frule_tac h = xa in ideal_subset [of "R" "J"], assumption+)
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (simp add:rHom_mem)
 apply (frule ideal_zero [of "R" "J"], assumption+)
 apply (simp add:image_def) apply blast
apply (rule ballI)+
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>s\<in>J. \<forall>t\<in>J. x = pj R I s \<and> y = pj R I t \<longrightarrow>
        (\<exists>xa\<in>J.  x +\<^sub>R /\<^sub>r I -\<^sub>R /\<^sub>r I y = pj R I xa)")
 apply blast apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply simp
 apply (frule pj_Hom [of "R" "I"], assumption+)
 apply (frule_tac h = s in ideal_subset [of "R" "J"], assumption+) 
 apply (frule_tac h = t in ideal_subset [of "R" "J"], assumption+)
 apply (simp add:rHom_def)   apply (erule conjE)+
   apply (frule ring_is_ag)
 apply (frule qring_ring [of "R" "I"], assumption+)
 apply (frule ring_is_ag [of "R /\<^sub>r I"])
  apply (frule_tac x = t in ag_mOp_closed [of "R"], assumption+)
 apply (frule_tac a1 = s and b1 = "-\<^sub>R t" in aHom_add [of "R" "R /\<^sub>r I" 
  "pj R I", THEN sym], assumption+) apply (simp add:aHom_inv_inv)
 apply (frule_tac x = t in ideal_inv1_closed [of "R" "J"], assumption+)
 apply (frule_tac x = s and y = "-\<^sub>R t" in ideal_pOp_closed [of "R" "J"], assumption+)
 apply blast
apply (rule ballI)+
apply (simp add:qring_def)
 apply (subgoal_tac "set_r_cos (b_ag R) I = set_ar_cos R I")
 apply simp apply (thin_tac "set_r_cos (b_ag R) I = set_ar_cos R I")
 apply (simp add:set_ar_cos_def)
 apply (subgoal_tac "\<forall>a\<in>carrier R. r = a \<uplus>\<^sub>R I \<longrightarrow>  rcostOp R I r x \<in> pj R I ` J") apply blast apply (thin_tac "\<exists>a\<in>carrier R. r = a \<uplus>\<^sub>R I")
 apply (rule ballI) apply (rule impI) apply simp
 apply (simp add:image_def)
 apply (subgoal_tac "\<forall>xa\<in>J. x = pj R I xa \<longrightarrow>
         (\<exists>xa\<in>J. rcostOp R I (a \<uplus>\<^sub>R I) x = pj R I xa)") apply blast
 apply (thin_tac "\<exists>xa\<in>J. x = pj R I xa") apply (rule ballI)
 apply (rule impI)
 apply (frule_tac x = xa in pj_mem [of "R" "I"], assumption+) 
 apply (simp add:ideal_subset) apply simp
 apply (subst rcostOp, assumption+)
 apply (simp add:ideal_subset)  
 apply (frule_tac x = xa and r = a in ideal_ring_multiple [of "R" "J"],
                                                  assumption+)
 apply (frule_tac h = "a \<cdot>\<^sub>R xa" in ideal_subset [of "R" "J"], assumption+)
 apply (frule_tac x1 = "a \<cdot>\<^sub>R xa" in pj_mem [THEN sym, of "R" "I"], assumption+)
 apply simp
 apply blast
apply (simp add:set_ar_cos_def)
 apply (frule ring_is_ag)
 apply (simp add:ag_carrier_carrier [THEN sym])
 apply (simp add:ar_coset_def set_r_cos_def)
done
 
lemma npQring:"\<lbrakk> ring R; ideal R I; a \<in> carrier R \<rbrakk> \<Longrightarrow>
      npow (qring R I) (a \<uplus>\<^sub>R I) n = (npow R a n) \<uplus>\<^sub>R I"
apply (induct_tac n)
apply (simp add:qring_def) 

apply (simp add:qring_def)
apply (rule rcostOp, assumption+)
apply (rule npClose, assumption+)
done

section "5. Primary ideals, Prime ideals"

constdefs
  maximal_set::"['a set set, 'a set] \<Rightarrow> bool"
 "maximal_set S mx == mx \<in> S \<and> (\<forall>s\<in>S. mx \<subseteq> s \<longrightarrow> mx = s)" 

constdefs
 nilpotent::"[('a, 'more) RingType_scheme, 'a] \<Rightarrow> bool"
  "nilpotent R a == \<exists>n\<in>NSet. a^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R"

 zero_divisor::"[('a, 'more) RingType_scheme, 'a] \<Rightarrow> bool"
  "zero_divisor R a == \<exists>x\<in> carrier R. x \<noteq> 0\<^sub>R \<and> x \<cdot>\<^sub>R a = 0\<^sub>R"

 primary_ideal::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> bool"
   "primary_ideal R q == ideal R q \<and> (1\<^sub>R) \<notin> q \<and> 
   (\<forall>x\<in> carrier R. \<forall>y\<in> carrier R. 
    x \<cdot>\<^sub>R y \<in> q  \<longrightarrow> (\<exists>n. (npow R x n) \<in> q \<or> y \<in> q))"

 prime_ideal::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> bool"
  "prime_ideal R p == ideal R p \<and> (1\<^sub>R) \<notin> p \<and> (\<forall>x\<in> carrier R. \<forall>y\<in> carrier R. 
   (x \<cdot>\<^sub>R y \<in> p \<longrightarrow> x \<in> p \<or> y \<in> p))"

 maximal_ideal::"[('a, 'more) RingType_scheme, 'a set] \<Rightarrow> bool"
  "maximal_ideal R mx == ideal R mx \<and> 1\<^sub>R \<notin> mx \<and> 
        {J. (ideal R J \<and> mx \<subseteq> J)} = {mx, carrier R}"

lemma maximal_ideal_ideal:"\<lbrakk> ring R; maximal_ideal R mx\<rbrakk> \<Longrightarrow> ideal R mx" 
apply (simp add:maximal_ideal_def)
done

lemma prime_is_primary:"\<lbrakk> ring R; prime_ideal R p \<rbrakk> \<Longrightarrow> 
   primary_ideal R p"
apply (unfold primary_ideal_def)
apply (rule conjI) apply (simp add:prime_ideal_def)
apply (rule conjI) apply (simp add:prime_ideal_def)
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (simp add:prime_ideal_def) apply (rotate_tac 2)
apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "ideal R p \<and> 1\<^sub>R \<notin> p \<and>
             (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> p \<longrightarrow> x \<in> p \<or> y \<in> p)")
apply (case_tac "y \<in> p") apply simp apply simp
apply (subgoal_tac "x \<in> p")
apply (subgoal_tac "npow R x 1 = x ")
apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>1 \<in> p") apply (thin_tac "x^\<^sup>R\<^sup> \<^sup>1 = x")
apply blast apply simp apply simp apply (simp add:ring_r_one) apply blast
done
  
lemma maximal_prime_Tr0:"\<lbrakk>ring R; maximal_ideal R mx; x \<in> carrier R; x \<notin> mx \<rbrakk> \<Longrightarrow>
    mx \<^bold>+\<^sub>R (R \<diamondsuit> x) = carrier R"
apply (frule principal_ideal [of "R" "x"], assumption+)
apply (frule sum_ideals [of "R" "mx" "R \<diamondsuit> x"])
 apply (simp add:maximal_ideal_def) apply assumption
 apply (frule sum_ideals_la1 [of "R" "mx" "R \<diamondsuit> x"])
  apply (simp add:maximal_ideal_def) apply assumption
apply (simp add:maximal_ideal_def) apply (erule conjE)+
apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x \<in> {J. ideal R J \<and> mx \<subseteq> J}")
 apply simp
apply (frule sum_ideals_la2 [of "R" "mx" "R \<diamondsuit> x"])
  apply (simp add:maximal_ideal_def) apply assumption+
  apply (frule a_in_principal [of "R" "x"], assumption+)
  apply (frule subsetD [of "R \<diamondsuit> x" "mx \<^bold>+\<^sub>R R \<diamondsuit> x" "x"], assumption+)
 apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x \<noteq> mx") apply simp
apply (thin_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x = mx \<or> mx \<^bold>+\<^sub>R R \<diamondsuit> x = carrier R")
 apply (thin_tac "R \<diamondsuit> x \<subseteq> mx \<^bold>+\<^sub>R R \<diamondsuit> x")
 apply (thin_tac "x \<in> R \<diamondsuit> x")
 apply (thin_tac "mx \<subseteq> mx \<^bold>+\<^sub>R R \<diamondsuit> x")
 apply (rule contrapos_pp) apply simp apply simp
apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
apply simp
done

lemma maximal_is_prime:"\<lbrakk> ring R; maximal_ideal R mx \<rbrakk> \<Longrightarrow> prime_ideal R mx"
apply (simp add:prime_ideal_def)
apply (unfold maximal_ideal_def) apply (frule conj_1)
apply (fold maximal_ideal_def) apply simp
apply (rule contrapos_pp) apply simp+
 apply (case_tac "1\<^sub>R \<in> mx") apply (simp add:maximal_ideal_def)
apply simp
apply (subgoal_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> mx \<and> x \<notin> mx \<and> y \<notin> mx \<longrightarrow> False") apply blast 
 apply (thin_tac "\<exists>x\<in>carrier R. \<exists>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> mx \<and> x \<notin> mx \<and> y \<notin> mx")
apply (rule ballI)+ apply (rule impI)
apply (erule conjE)+
apply (subgoal_tac "1\<^sub>R \<in> mx") apply simp
apply (frule maximal_prime_Tr0 [of "R" "mx" _], assumption+)
 apply (subgoal_tac "1\<^sub>R \<in> mx \<^bold>+\<^sub>R R \<diamondsuit> x")
 apply (thin_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x = carrier R") 
 apply (frule_tac x = y in maximal_prime_Tr0 [of "R" "mx"], assumption+)
 apply (frule ring_one) apply (subgoal_tac "1\<^sub>R \<in> mx \<^bold>+\<^sub>R R \<diamondsuit> y")
 apply (thin_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> y = carrier R") 
prefer 2 apply simp
prefer 2 apply simp apply (simp add:ring_one)
 
apply (simp add:asettOp_def settOp_def)
 apply (frule ring_is_ag[of "R"])
apply (subgoal_tac "\<forall>xa\<in>mx. \<forall>ya\<in>R \<diamondsuit> x.  \<forall>xb\<in>mx. \<forall>yb\<in>R \<diamondsuit> y. GroupType.tOp (b_ag R) xa  ya = 1\<^sub>R \<and> GroupType.tOp (b_ag R) xb yb = 1\<^sub>R \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>xa\<in>mx. \<exists>y\<in>R \<diamondsuit> x.  GroupType.tOp (b_ag R) xa y = 1\<^sub>R")
 apply (thin_tac "\<exists>x\<in>mx. \<exists>y\<in>R \<diamondsuit> y.  GroupType.tOp (b_ag R) x y = 1\<^sub>R")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)+
apply (frule ring_is_ag [of "R"])
apply (frule agop_gop [of "R"]) apply simp
 apply (subgoal_tac "(xa +\<^sub>R ya) \<cdot>\<^sub>R (xb +\<^sub>R yb) = 1\<^sub>R") prefer 2 apply simp
 apply (rule ring_l_one, assumption+)
 apply (thin_tac "xa +\<^sub>R ya = 1\<^sub>R") apply (thin_tac "xb +\<^sub>R yb = 1\<^sub>R")
 apply (frule_tac a = xa and b = ya and x = xb and y = yb in 
  ring_distrib3 [of "R"])
 apply (rule ideal_subset, assumption+) 
 apply (frule_tac a = x in principal_ideal [of "R"], assumption+)
 apply (frule_tac I = "R \<diamondsuit> x" and  h = ya in ideal_subset [of "R"], assumption+)
 apply (rule ideal_subset, assumption+) 
 apply (frule_tac a = y in principal_ideal [of "R"], assumption+)
 apply (frule_tac I = "R \<diamondsuit> y" and  h = yb in ideal_subset [of "R"], assumption+)
apply simp
 apply (thin_tac "( xa +\<^sub>R ya) \<cdot>\<^sub>R ( xb +\<^sub>R yb) = 1\<^sub>R")
apply (subgoal_tac " xa \<cdot>\<^sub>R xb +\<^sub>R  xa \<cdot>\<^sub>R yb +\<^sub>R  ya \<cdot>\<^sub>R xb +\<^sub>R  ya \<cdot>\<^sub>R yb \<in> mx")
 apply simp
 apply (rule ideal_pOp_closed, assumption+)+ 
 apply (rule ideal_ring_multiple, assumption+)
 apply (simp add:ideal_subset)
apply (rule ideal_ring_multiple1, assumption+)
apply (rule_tac I =  "R \<diamondsuit> y" and h = yb in ideal_subset [of "R"], assumption+)
 apply (simp add:principal_ideal) apply assumption
apply (rule ideal_ring_multiple, assumption+)
apply (rule_tac I =  "R \<diamondsuit> x" and h = ya in ideal_subset [of "R"], assumption+)
 apply (simp add:principal_ideal) apply assumption 
 apply (thin_tac "xa \<cdot>\<^sub>R xb +\<^sub>R  xa \<cdot>\<^sub>R yb +\<^sub>R  ya \<cdot>\<^sub>R xb +\<^sub>R  ya \<cdot>\<^sub>R yb = 1\<^sub>R")
 apply (thin_tac "GroupType.tOp (b_ag R) = pOp R") apply (rotate_tac -1)
apply (simp add:Rxa_def) 
 apply (subgoal_tac "\<forall>r\<in>carrier R. \<forall>s\<in>carrier R. ya =  r \<cdot>\<^sub>R x \<and> yb =  s \<cdot>\<^sub>R y
  \<longrightarrow> ya \<cdot>\<^sub>R yb \<in> mx") apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. ya =  r \<cdot>\<^sub>R x")
 apply (thin_tac "\<exists>r\<in>carrier R. yb =  r \<cdot>\<^sub>R y")
apply (rule ballI)+ apply (rule impI) apply (erule conjE) 
 apply simp
 apply (simp add:ring_tOp_rel)
apply (rule_tac x = "x \<cdot>\<^sub>R y" and r = "r \<cdot>\<^sub>R s" in ideal_ring_multiple [of "R" "mx"], assumption+)
 apply (simp add:ring_tOp_closed)
done

lemma chain_un:"\<lbrakk> ring R; c \<in> chain {I. ideal R I \<and> I \<subset> carrier R}; c \<noteq> {}\<rbrakk>
 \<Longrightarrow> ideal R (\<Union>c)"
apply (rule ideal_condition, assumption+) 
apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>I\<in>c. x \<in> I \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "Bex c (op \<in> x)")
apply (rule ballI) apply (rule impI) 
 apply (simp add:chain_def)
 apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subset> carrier R} \<and>
             (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
apply (thin_tac "\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x")
apply (frule subsetD [of "c" "{I. ideal R I \<and> I \<subset> carrier R}" _], assumption+)
 apply (simp add:CollectI) 
 apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subset> carrier R}")
 apply (thin_tac "I \<in> c")
 apply (subgoal_tac "ideal R I")
 apply (rule ideal_subset, assumption+) apply simp
apply (simp add:chain_def) apply (frule conj_1)
 apply (thin_tac " c \<subseteq> {I. ideal R I \<and> I \<subset> carrier R} \<and> (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
 apply (subgoal_tac "\<exists>X. X \<in> c")
 apply (subgoal_tac "\<forall>Y. Y\<in>c \<longrightarrow> Y \<noteq> {}") apply blast 
 apply (thin_tac "\<exists>X. X \<in> c")
 apply (rule allI) apply (rule impI) 
 apply (frule subsetD [of "c" "{I. ideal R I \<and> I \<subset> carrier R}" _])
  apply assumption+ 
  apply (simp add:CollectI) apply (frule conj_1)
apply (frule ideal_zero [of "R" _], assumption+)
 apply blast
 apply blast

apply (rule ballI)+
 apply (simp add:CollectI)
apply (subgoal_tac "\<forall>X\<in>c. \<forall>Y\<in>c. x \<in> X \<and> y \<in> Y \<longrightarrow> x +\<^sub>R -\<^sub>R y \<in> \<Union>c")
apply blast 
 apply (thin_tac "Bex c (op \<in> x)") apply (thin_tac "Bex c (op \<in> y)")
apply (rule ballI)+ apply (rule impI)
apply (simp add:chain_def)
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subset> carrier R} \<and> (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
 apply (subgoal_tac "ideal R X")
 apply (subgoal_tac "ideal R Y")
 apply (subgoal_tac "X \<subseteq> Y \<or> Y \<subseteq> X")
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> X \<and> y \<in> Y")
apply (case_tac "X \<subseteq> Y")
apply (subgoal_tac "x +\<^sub>R -\<^sub>R y \<in> Y")
 apply blast
 apply (rule ideal_pOp_closed, assumption+)
 apply (rule subsetD, assumption+)
 apply (rule ideal_inv1_closed, assumption+) 
apply (rotate_tac -1) apply simp
apply (subgoal_tac "x +\<^sub>R -\<^sub>R y \<in> X")
 apply blast
 apply (rule ideal_pOp_closed, assumption+)
 apply (rule subsetD, assumption+)
 apply (rule ideal_inv1_closed, assumption+) 
apply simp
apply blast
apply blast

apply (rule ballI)+
 apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>X\<in>c. x \<in> X \<longrightarrow> ( r \<cdot>\<^sub>R x) \<in> X") apply blast
 apply (thin_tac "Bex c (op \<in> x)")
apply (rule ballI)
apply (rule impI)
 apply (subgoal_tac "ideal R X")
 apply (simp add:ideal_ring_multiple)
 apply (simp add:chain_def)
apply blast
done

lemma id_maximal_Exist:"\<lbrakk>ring R; \<not>(zeroring R)\<rbrakk> \<Longrightarrow> \<exists>I. maximal_ideal R I"

 apply (cut_tac S="{ I. ideal R I \<and> I \<subset> carrier R }" in Zorn_Lemma2)
 apply (rule ballI) 

 apply (case_tac "c={}", simp)
   apply (subgoal_tac "ideal R {0\<^sub>R}")
   apply (subgoal_tac "{0\<^sub>R} \<subset> carrier R")
  apply blast
  apply (subgoal_tac "{0\<^sub>R} \<subseteq> carrier R")
  apply (subgoal_tac "1\<^sub>R \<in> carrier R") apply (subgoal_tac "1\<^sub>R \<noteq> 0\<^sub>R")
  apply (subgoal_tac "{0\<^sub>R} \<noteq> carrier R")
  apply (simp add:psubset_def) apply (rule contrapos_pp) apply simp+
  apply (subgoal_tac "1\<^sub>R \<in> {0\<^sub>R}") apply (thin_tac "{0\<^sub>R} = carrier R")
  apply simp apply simp
  apply (rule contrapos_pp) apply simp+ 
  apply (subgoal_tac "zeroring R ") apply simp
  apply (rule Zero_ring) apply assumption+ apply (simp add:ring_def)
  apply (simp add:ring_def agroup_def)
  apply (simp add:zero_ideal)

  (*  case  c \<noteq> {}  *)
  apply (subgoal_tac "ideal R (\<Union> c)")
  apply (subgoal_tac "\<Union> c \<subset> carrier R")
  apply (subgoal_tac "\<forall>x\<in>c. x \<subseteq> \<Union> c") apply blast
    (* prove \<forall>x\<in>c. x \<subseteq> \<Union>c *)
  apply (rule ballI) 
  apply (rule subsetI) apply simp apply blast
  apply (rule contrapos_pp) apply simp+ apply (simp add:psubset_def)
  apply (subgoal_tac "\<Union>c \<subseteq> carrier R") apply simp
  apply (subgoal_tac "1\<^sub>R \<in> carrier R")  apply (subgoal_tac "1\<^sub>R \<in>  \<Union>c")
   apply (thin_tac "\<Union>c = carrier R")
   apply (thin_tac "1\<^sub>R \<in> carrier R")
  apply simp
  apply (subgoal_tac "\<forall>X\<in>c. 1\<^sub>R \<in> X \<longrightarrow> False") apply blast
   apply (thin_tac "Bex c (op \<in> (1\<^sub>R))")
  apply (rule ballI) apply (rule impI) 
  apply (simp add:chain_def)
  apply (subgoal_tac "X\<in>{I. ideal R I \<and> I\<subseteq> carrier R \<and> I \<noteq> carrier R}")
  apply simp   apply (subgoal_tac "X = carrier R") 
  apply simp
  apply (rule  ideal_inc_one, assumption+) apply simp apply simp
  apply (frule conj_1)
   apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subseteq> carrier R \<and> I \<noteq> carrier R} 
           \<and> (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
  apply (rule subsetD) apply simp apply assumption
  apply simp apply (simp add:ring_def)
apply (rule subsetI) apply simp 
  apply (subgoal_tac "\<forall>X\<in>c. x\<in>X \<longrightarrow> x\<in>carrier R") apply blast
    apply (thin_tac "Bex c (op \<in> x)")
  apply (rule ballI) apply (rule impI)
   apply (subgoal_tac "ideal R X") apply (simp add:ideal_subset)
   apply (simp add:chain_def)
   apply (frule conj_1)
    apply (thin_tac "c \<subseteq> {I. ideal R I \<and> I \<subseteq> carrier R \<and> I \<noteq> carrier R}
    \<and> (\<forall>x\<in>c. \<forall>y\<in>c. x \<subseteq> y \<or> y \<subseteq> x)")
   apply (subgoal_tac "X\<in>{I. ideal R I\<and>I \<subseteq> carrier R \<and> I \<noteq> carrier R}")
   apply simp
   apply (rule subsetD) apply simp apply assumption
(* prove ideal R (\<Union>c) *)
apply (simp add:chain_un)
 apply (subgoal_tac " \<forall>y\<in>{I. ideal R I \<and> I \<subset> carrier R}. (\<forall>x\<in>{I. ideal R I \<and> I \<subset> carrier R}. y \<subseteq> x \<longrightarrow> y = x) \<longrightarrow> (\<exists>I. maximal_ideal R I)")
 apply blast
 apply (thin_tac "\<exists>y\<in>{I. ideal R I \<and> I \<subset> carrier R}.
          \<forall>x\<in>{I. ideal R I \<and> I \<subset> carrier R}. y \<subseteq> x \<longrightarrow> y = x")
apply (rule ballI) apply (rule impI)
 apply (subgoal_tac "maximal_ideal R y") apply blast
 apply (simp add:maximal_ideal_def)
 apply (erule conjE)
 apply (rename_tac Y) apply (rule conjI)
 apply (rule contrapos_pp) apply simp+
apply (frule_tac  R = R and I = Y in ideal_inc_one, assumption+)
 apply (simp add:psubset_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (case_tac "x = carrier R")  apply simp apply simp
 apply (simp add:psubset_def) 
 apply (subgoal_tac "ideal R x") apply (subgoal_tac "x \<subseteq> carrier R")
 apply blast
 apply (simp add:ideal_subset1) apply simp
 apply auto apply (simp add:whole_ideal) 
done

constdefs
 ideal_Int::"[('a, 'more) RingType_scheme, 'a set set] \<Rightarrow> 'a set"
  "ideal_Int R S == \<Inter> S"

lemma ideal_Int_ideal:"\<lbrakk>ring R; S \<subseteq> {I. ideal R I}; S\<noteq>{}\<rbrakk> \<Longrightarrow> ideal R (\<Inter> S)"

apply (rule ideal_condition, assumption+)
 apply (rule subsetI)
apply (subgoal_tac "\<forall>X\<in>S. X \<subseteq> carrier R")
apply blast
apply (rule ballI)
 apply (subgoal_tac "ideal R X")
 apply (rule subsetI) apply (simp add:ideal_subset)
apply blast
apply (subgoal_tac "\<forall>X. X\<in>S \<longrightarrow> 0\<^sub>R \<in> X")
apply blast
apply (rule allI) apply (rule impI)
apply (subgoal_tac "ideal R X")
apply (simp add:ideal_zero)
apply blast

apply (rule ballI)+
apply (subgoal_tac "\<forall>X\<in>S.  x +\<^sub>R -\<^sub>R y \<in> X")
apply blast
apply (rule ballI)
 apply (rule ideal_pOp_closed, assumption+)
 apply blast apply blast
 apply (rule ideal_inv1_closed, assumption+)
 apply blast
 apply blast

apply (rule ballI)+
apply (subgoal_tac "\<forall>X. X\<in>S \<longrightarrow> (\<forall>r\<in>carrier R. \<forall>x\<in>\<Inter>S.  r \<cdot>\<^sub>R x \<in> X)")
apply blast
apply (rule allI) apply (rule impI)
apply (rule ballI)+
 apply (rule ideal_ring_multiple, assumption+)
 apply blast
 apply blast
 apply assumption
done

lemma sum_prideals_Int:"\<lbrakk>ring R; \<forall>l\<in>Nset n. f l \<in> carrier R; S = {I. ideal R I \<and> f ` (Nset n) \<subseteq> I}\<rbrakk> \<Longrightarrow>  (sum_pr_ideals R f n) = \<Inter> S"
apply (rule equalityI) 
apply (subgoal_tac "\<forall>X\<in>S. sum_pr_ideals R f n \<subseteq> X")
apply blast
 apply (rule ballI)
 apply (simp add:CollectI)
 apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "ideal R X \<and> f ` Nset n \<subseteq> X") 
 apply (simp add:sum_of_prideals4)
apply (subgoal_tac "(sum_pr_ideals R f n) \<in> S")
apply blast
apply (simp add:CollectI)
apply (simp add: sum_of_prideals2)
apply (simp add: sum_of_prideals)
done

text{* This proves that (sum_pr_ideals R f n) is the smallest ideal containing
 f ` (Nset n) *} 

constdefs
 ideal_prod::"['a set, ('a, 'more) RingType_scheme, 'a set] \<Rightarrow> 'a set"
               ("(3_/ \<diamondsuit>\<^sub>_/ _)" [98,98,99]98)
 " I \<diamondsuit>\<^sub>R J == \<Inter>{K. ideal R K \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>R j}\<subseteq> K}"

consts
 ideal_n_prod::"[('a, 'm) RingType_scheme, nat,  nat \<Rightarrow> 'a set] \<Rightarrow> 'a set"

primrec
  ideal_n_prod0: "ideal_n_prod R 0 J = J 0"
  ideal_n_prodSn: "ideal_n_prod R (Suc n) J = (ideal_n_prod R n J) \<diamondsuit>\<^sub>R (J (Suc n))"

syntax
 "@IDNPROD"::"[('a, 'm) RingType_scheme, nat,  nat \<Rightarrow> 'a set] \<Rightarrow> 'a set"
          ("(3i\<Pi>\<^sub>_\<^sub>,\<^sub>_ _)" [98,98,99]98)
translations
  "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J" == "ideal_n_prod R n J"

consts
  ideal_pow :: "['a set, ('a, 'more) RingType_scheme, nat] \<Rightarrow> 'a set"
               ("(3_/ \<^sup>\<diamondsuit>\<^sup>_/ \<^sup>_)" [120,120,121]120)
primrec
 ip0:  "I \<^sup>\<diamondsuit>\<^sup>R \<^sup>0 = carrier R"
 ipSuc:  "I \<^sup>\<diamondsuit>\<^sup>R \<^sup>(Suc n) = I \<diamondsuit>\<^sub>R (I \<^sup>\<diamondsuit>\<^sup>R \<^sup>n)"


lemma ideal_prod_ideal:"\<lbrakk>ring R; ideal R I; ideal R J \<rbrakk> \<Longrightarrow> 
                                ideal R (I \<diamondsuit>\<^sub>R J)" 
apply (simp add:ideal_prod_def)
apply (subgoal_tac "(carrier R)\<in>{K. ideal R K \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>R j}
    \<subseteq> K}")
apply (subgoal_tac "{K. ideal R K \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x = i \<cdot>\<^sub>R j} \<subseteq> K} \<noteq> {}")
apply (rule ideal_Int_ideal) apply assumption
apply (rule subsetI) apply (simp add:CollectI) apply assumption
apply blast
apply (simp add:CollectI)
apply (simp add:whole_ideal)
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>I. \<forall>j\<in>J. x =  i \<cdot>\<^sub>R j \<longrightarrow> x \<in> carrier R")
 apply blast apply (thin_tac "\<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j")
apply auto
apply (simp add:ideal_subset ring_tOp_closed)
done

lemma n_prod_idealTr:"ring R \<Longrightarrow> 
    (\<forall>k\<in>Nset n. ideal R (J k)) \<longrightarrow> ideal R (ideal_n_prod R n J)"
apply (induct_tac n)
apply (rule impI)
apply simp
apply (simp add:Nset_def)

apply (rule impI)
apply (simp only:ideal_n_prodSn)
 apply (subgoal_tac "\<forall>k\<in>Nset n. ideal R (J k)")
 apply (rule ideal_prod_ideal, assumption+)
 apply simp
 apply (simp add:Nset_def)
 apply (rule ballI) apply (subgoal_tac "k \<in> Nset (Suc n)")
 apply (rotate_tac -1)
 apply simp
apply (simp add:Nset_def)
done
 
lemma n_prod_ideal:"\<lbrakk>ring R; \<forall>k\<in>(Nset n). ideal R (J k)\<rbrakk>
                    \<Longrightarrow>  ideal R (ideal_n_prod R n J)"
apply (simp add:n_prod_idealTr)
done

lemma ideal_prod_la1:"\<lbrakk>ring R; ideal R I; ideal R J \<rbrakk> \<Longrightarrow> (I \<diamondsuit>\<^sub>R J) \<subseteq> I" 
 apply (simp add:ideal_prod_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "{x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j} \<subseteq> I")
 apply blast
apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j} \<subseteq> xa
                                                              \<longrightarrow> x \<in> xa") 
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply auto
 apply (rule ideal_ring_multiple1, assumption+)
 apply (simp add:ideal_subset)
done

lemma ideal_prod_el1:"\<lbrakk>ring R; ideal R I; ideal R J; a \<in> (I \<diamondsuit>\<^sub>R J)\<rbrakk> \<Longrightarrow> a \<in> I" 
apply (frule ideal_prod_la1 [of "R" "I" "J"], assumption+)
apply (rule subsetD, assumption+)
done

lemma ideal_prod_la2:"\<lbrakk>ring R; ideal R I; ideal R J \<rbrakk> \<Longrightarrow> (I \<diamondsuit>\<^sub>R J) \<subseteq> J" 
 apply (simp add:ideal_prod_def)
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply (subgoal_tac "{x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j} \<subseteq> J")
 apply blast
apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j} \<subseteq> xa
                                                              \<longrightarrow> x \<in> xa") 
 apply (rule subsetI)
 apply (simp add:CollectI)
 apply auto
 apply (rule ideal_ring_multiple, assumption+)
 apply (simp add:ideal_subset)
done

lemma ideal_prod_el2:"\<lbrakk>ring R; ideal R I; ideal R J; a \<in> (I \<diamondsuit>\<^sub>R J)\<rbrakk> \<Longrightarrow> a \<in> J" 
apply (frule ideal_prod_la2 [of "R" "I" "J"], assumption+)
apply (rule subsetD, assumption+)
done

lemma ele_n_prodTr0:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc n). ideal R (J k);
             a \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J \<rbrakk> \<Longrightarrow> a \<in> (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) \<and> a \<in> (J (Suc n))"
apply (rule conjI)
apply simp
apply (rule ideal_prod_el1 [of "R" "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J" "J (Suc n)"], assumption+)
apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in> Nset (Suc n)")
 apply (simp add:n_prod_ideal)
 apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)
 apply assumption
apply (rule ideal_prod_el2 [of "R" "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J" "J (Suc n)"], assumption+)
apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in> Nset (Suc n)")
 apply (simp add:n_prod_ideal)
 apply (rule allI) apply (rule impI) apply (simp add:Nset_def)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply simp apply (simp add:Nset_def)
 apply simp
done

lemma ele_n_prodTr1:"ring R \<Longrightarrow> ((\<forall>k\<in>(Nset n). ideal R (J k)) \<and> a\<in> ideal_n_prod R n J) \<longrightarrow>  (\<forall>k\<in>(Nset n). a \<in> (J k))"
apply (induct_tac n)
(** n = 0 **)
 apply simp
 apply (rule impI)
 apply (simp add:Nset_def)
(** n **)
apply (rule impI)
 apply (rule ballI)
 apply (subgoal_tac "\<forall>k. k\<in> (Nset n) \<longrightarrow> k \<in> (Nset (Suc n))")
 apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "(\<forall>k\<in>Nset (Suc n). ideal R (J k)) \<and> a \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>(Suc n) J")
 apply (frule ele_n_prodTr0, assumption+)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "a \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<and> a \<in> J (Suc n)")
apply (case_tac "k \<in> Nset n")
 apply blast
apply (thin_tac "(\<forall>k\<in>Nset n. ideal R (J k)) \<and> a \<in> i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<longrightarrow>
             (\<forall>k\<in>Nset n. a \<in> J k)")
apply (subgoal_tac "k = Suc n")
 apply simp
apply (simp add:Nset_def)
apply (rule allI) apply (rule impI)
apply (simp add:Nset_def)
done

lemma ele_n_prod:"\<lbrakk>ring R; \<forall>k\<in>(Nset n). ideal R (J k); a \<in> ideal_n_prod R n J \<rbrakk> \<Longrightarrow>  \<forall>k\<in>(Nset n). a \<in> (J k)"
apply (simp add: ele_n_prodTr1 [of "R" "n" "J" "a"])
done

lemma ideal_pow_ideal:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> ideal R (I \<^sup>\<diamondsuit>\<^sup>R \<^sup>n)"
apply (induct_tac n)
apply simp apply (simp add:whole_ideal)
apply simp
apply (simp add:ideal_prod_ideal)
done

lemma ideal_prod_prime:"\<lbrakk> ring R; ideal R I; ideal R J; prime_ideal R P;
 I \<diamondsuit>\<^sub>R J \<subseteq> P \<rbrakk> \<Longrightarrow> I \<subseteq> P \<or> J \<subseteq> P"
apply (rule contrapos_pp) apply simp+
apply (frule conj_1) apply (frule conj_2) 
 apply (thin_tac "\<not> I \<subseteq> P \<and> \<not> J \<subseteq> P")
apply (subgoal_tac "\<exists>i\<in>I. i \<notin> P")
apply (subgoal_tac "\<exists>j\<in>J. j \<notin> P")
apply (subgoal_tac "\<forall>i\<in>I. \<forall>j\<in>J. i \<notin> P \<and> j \<notin> P \<longrightarrow> False") 
 apply blast
 apply (thin_tac "\<exists>i\<in>I. i \<notin> P") apply (thin_tac "\<exists>j\<in>J. j \<notin> P")
apply (rule ballI)+ apply (rule impI)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "i \<notin> P \<and> j \<notin> P") apply (thin_tac "\<not> I \<subseteq> P")
 apply (thin_tac "\<not> J \<subseteq> P")
apply (subgoal_tac "i \<cdot>\<^sub>R j \<in> P") apply (subgoal_tac "i \<in> P \<or> j \<in> P")
apply blast
apply (subgoal_tac "i \<in> carrier R") apply (subgoal_tac "j \<in> carrier R")
 apply (thin_tac "i \<notin> P") apply (thin_tac "j \<notin> P")
apply (rotate_tac 7)
apply (simp add: prime_ideal_def) apply (simp add:ideal_subset)
 apply (simp add:ideal_subset)
apply (subgoal_tac "i \<cdot>\<^sub>R j \<in> I \<diamondsuit>\<^sub>R J") apply (simp add:subsetD)
apply (simp add:ideal_prod_def)
apply (rule allI) apply (rule impI)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "ideal R x \<and> {x. \<exists>i\<in>I. \<exists>j\<in>J. x =  i \<cdot>\<^sub>R j} \<subseteq> x")
apply blast apply blast apply blast
done

lemma ideal_n_prod_primeTr:"\<lbrakk> ring R; prime_ideal R P\<rbrakk> \<Longrightarrow> (\<forall>k\<in>Nset n. ideal R (J k)) \<longrightarrow> (ideal_n_prod R n J \<subseteq> P) \<longrightarrow> (\<exists>i\<in>Nset n. (J i) \<subseteq> P)"
apply (induct_tac n)
apply (simp add:Nset_def)
apply (rule impI)
apply simp
 apply (rule impI)
apply (subgoal_tac "ideal R (i\<Pi>\<^sub>R\<^sub>,\<^sub>n J)")
apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> P \<or> J (Suc n) \<subseteq> P")
apply (case_tac "J (Suc n) \<subseteq> P")
apply (subgoal_tac "Suc n \<in> Nset (Suc n)")
 apply blast apply (simp add:Nset_def)
apply (subgoal_tac "\<forall>l. l \<in> (Nset n) \<longrightarrow> l \<in> Nset (Suc n)") 
apply (subgoal_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> P")
 apply (thin_tac "i\<Pi>\<^sub>R\<^sub>,\<^sub>n J \<subseteq> P \<or> J (Suc n) \<subseteq> P")
 apply (thin_tac "\<not> J (Suc n) \<subseteq> P")
 apply (thin_tac "(i\<Pi>\<^sub>R\<^sub>,\<^sub>n J) \<diamondsuit>\<^sub>R (J (Suc n)) \<subseteq> P")
 apply blast
apply simp apply (simp add:Nset_def)
apply (rule ideal_prod_prime, assumption+)
 apply (subgoal_tac "Suc n \<in> Nset (Suc n)") apply (rotate_tac -1) 
 apply simp apply (simp add:Nset_def)
 apply assumption+
 apply (subgoal_tac "\<forall>l. l\<in>Nset n \<longrightarrow> l \<in> Nset (Suc n)")
 apply (simp add:n_prod_ideal)
apply (simp add:Nset_def)
done

lemma ideal_n_prod_prime:"\<lbrakk> ring R; prime_ideal R P; \<forall>k\<in>Nset n. ideal R (J k); ideal_n_prod R n J \<subseteq> P\<rbrakk> \<Longrightarrow> \<exists>i\<in>Nset n. (J i) \<subseteq> P"
apply (simp add:ideal_n_prod_primeTr)
done

constdefs
 ppa::"[('a, 'more) RingType_scheme, nat \<Rightarrow> 'a set, 'a set, 
                               nat] \<Rightarrow> (nat \<Rightarrow> 'a)"
  "ppa R P A i l == SOME x. x \<in> A \<and> x \<in> (P (skip i l)) \<and> x \<notin> P i"  
     (** Note (ppa R P A) is used to prove prime_ideal_cont1 **) 

lemma prod_primeTr:"\<lbrakk> ring R; prime_ideal R P; ideal R A; \<not> A \<subseteq> P; ideal R B; \<not> B \<subseteq> P \<rbrakk> \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B \<and> x \<notin> P"  
apply (subgoal_tac "\<exists>a. a \<in> A \<and> a \<notin> P")
apply (subgoal_tac "\<exists>b. b \<in> B \<and> b \<notin> P")
apply (subgoal_tac "\<forall>a. \<forall>b. (a \<in> A \<and> a \<notin> P) \<and> (b \<in> B \<and> b \<notin> P) \<longrightarrow>
                        (\<exists>x. x \<in> A \<and> x \<in> B \<and> x \<notin> P)")
 apply blast
 apply (thin_tac "\<exists>a. a \<in> A \<and> a \<notin> P")
 apply (thin_tac "\<exists>b. b \<in> B \<and> b \<notin> P")
 apply (rule allI)+
 apply (rule impI) apply (erule conjE)+
apply (subgoal_tac "a \<cdot>\<^sub>R b \<in> A \<and> a \<cdot>\<^sub>R b \<in> B \<and> a \<cdot>\<^sub>R b \<notin> P")
 apply blast
 apply (rule conjI)
 apply (rule ideal_ring_multiple1, assumption+)
  apply (simp add:ideal_subset)
 apply (rule conjI)
  apply (rule ideal_ring_multiple, assumption+)
  apply (simp add:ideal_subset)
 apply (simp add:prime_ideal_def)
 apply (erule conjE)+
 apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "a \<in> carrier R")
apply (subgoal_tac "b \<in> carrier R")
 apply (subgoal_tac "a \<in> P \<or> b \<in> P") apply simp
  apply (thin_tac "a \<notin> P") apply (thin_tac "b \<notin> P")
 apply simp
 apply (simp add:ideal_subset)
 apply (simp add:ideal_subset)
apply blast
apply blast
done
 
lemma prod_primeTr1:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc n). prime_ideal R (P k); ideal R A; \<forall>l\<in>Nset (Suc n). \<not> (A \<subseteq> P l); \<forall>k\<in>Nset (Suc n). \<forall>l\<in>Nset (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l); i \<in> Nset (Suc n)\<rbrakk> \<Longrightarrow> \<forall>l\<in>Nset n. ppa R P A i l \<in> A \<and> ppa R P A i l \<in> (P (skip i l)) \<and> ppa R P A i l \<notin> (P i)"  
apply (rule ballI)
apply (subgoal_tac "\<not> A \<subseteq> P i")
apply (subgoal_tac "\<not> P (skip i l) \<subseteq> P i")
apply (subgoal_tac "\<exists>a. a \<in> A \<and> a \<in> P (skip i l) \<and> a \<notin> P i") 
 apply (simp add:ppa_def)
 apply (rule someI2_ex, assumption)
 apply assumption
 apply (rule prod_primeTr, assumption+)
 apply simp
 apply assumption+ 
 apply (subgoal_tac "prime_ideal R (P (skip i l))")
  apply (simp add:prime_ideal_def)
  apply (subgoal_tac "skip i l \<in> Nset (Suc n)")
  apply simp 
  apply (simp add:skip_mem)
  apply simp    
apply (frule skip_fun_im [of "i" "n"])
apply (subgoal_tac "skip i l \<in> Nset (Suc n) - {i}")
 apply (thin_tac "skip i  ` Nset n = Nset (Suc n) - {i}")
 apply blast 
 apply (subgoal_tac "skip i l \<in> (skip i) ` (Nset n)")
 apply simp apply (thin_tac "skip i ` Nset n = Nset (Suc n) - {i}")
 apply (simp add:image_def) apply blast
 apply simp
done

lemma ppa_mem:"\<lbrakk>ring R; \<forall>k\<in>Nset (Suc n). prime_ideal R (P k); ideal R A; \<forall>l\<in>Nset (Suc n). \<not> (A \<subseteq> P l); \<forall>k\<in>Nset (Suc n). \<forall>l\<in>Nset (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l); i \<in> Nset (Suc n); l \<in> Nset n\<rbrakk> \<Longrightarrow> ppa R P A i l \<in> carrier R"
apply (frule prod_primeTr1, assumption+)
 apply (subgoal_tac "ppa R P A i l \<in> A")
 apply (simp add:ideal_subset)
 apply simp
done

lemma nsum_memTr:"ring R \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> carrier R) \<longrightarrow> (\<forall>l\<in> Nset n. nsum0 R f l \<in> carrier R)"  
apply (induct_tac n)
(** n = 0 **)
 apply (rule impI)
 apply (rule ballI)
 apply (simp add:Nset_def)
(** n **)
apply (rule impI)
 apply (rule ballI)
 (** case l = Suc n **)
  apply (case_tac "l = Suc n")
  apply simp
  apply (rule ag_pOp_closed)
   apply (simp add:ring_def)
   apply simp
   apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in>Nset (Suc n)")
   apply (subgoal_tac "n \<in> Nset n")
  apply simp apply (simp add:Nset_def) apply (simp add:Nset_def)
 (** case l \<noteq> Suc n **)
  apply (subgoal_tac "l \<in> Nset n")
  apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in>Nset (Suc n)")
  apply simp apply (simp add:Nset_def)
   apply (thin_tac "(\<forall>i\<in>Nset n. f i \<in> carrier R) \<longrightarrow>
             (\<forall>l\<in>Nset n. nsum0 R f l \<in> carrier R)")
   apply (thin_tac "\<forall>i\<in>Nset (Suc n). f i \<in> carrier R")
 apply (simp add:Nset_def)
done

lemma nsum_mem:"\<lbrakk>ring R; \<forall>i\<in>Nset n. f i \<in> carrier R \<rbrakk> \<Longrightarrow>
                          \<forall>l\<in> Nset n. nsum0 R f l \<in> carrier R"  
apply (simp add:nsum_memTr)
done

lemma nsum_ideal_incTr:"\<lbrakk>ring R; ideal R A\<rbrakk> \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> A) \<longrightarrow>
  nsum0 R f n \<in> A"
 apply (induct_tac n)
 apply (rule impI)
  apply (simp add:Nset_def)
(** n **)
apply (rule impI)
apply simp
apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:Nset_def)
 apply (simp add:Nset_def)
done

lemma nsum_ideal_inc:"\<lbrakk>ring R; ideal R A; \<forall>i\<in>Nset n. f i \<in> A \<rbrakk> \<Longrightarrow>
  nsum0 R f n \<in> A"
apply (simp add:nsum_ideal_incTr)
done

lemma nsum_ideal_excTr:"\<lbrakk>ring R; ideal R A\<rbrakk> \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> carrier R) \<and> (\<exists>j\<in>Nset n. (\<forall>l\<in>Nset n -{j}. f l \<in> A) \<and> (f j \<notin> A)) \<longrightarrow> nsum0 R f n \<notin> A"
apply (induct_tac n)
(** n = 0 **)
 apply (simp add:Nset_def)
(** n **)
 apply (rule impI)
 apply (erule conjE)+ 
apply (subgoal_tac "\<forall>j\<in>Nset (Suc n). (\<forall>l\<in>Nset (Suc n) - {j}. f l \<in> A) \<and> f j \<notin> A \<longrightarrow> nsum0 R f (Suc n) \<notin> A")
 apply blast
 apply (thin_tac "\<exists>j\<in>Nset (Suc n). (\<forall>l\<in>Nset (Suc n) - {j}. f l \<in> A) \<and> f j \<notin> A")
 apply (rule ballI)
 apply (rule impI)
 apply (erule conjE)
apply (case_tac "j = Suc n")
 apply simp
  apply (thin_tac "(\<forall>i\<in>Nset n. f i \<in> carrier R) \<and>
             (\<exists>j\<in>Nset n. (\<forall>l\<in>Nset n - {j}. f l \<in> A) \<and> f j \<notin> A) \<longrightarrow>
             nsum0 R f n \<notin> A")
 apply (subgoal_tac "f (Suc n) \<in> carrier R")
 apply (subgoal_tac "Nset (Suc n) - {Suc n} = Nset n")
 apply simp
  apply (thin_tac "Nset (Suc n) - {Suc n} = Nset n")
 apply (rule contrapos_pp) apply simp+ 
 apply (subgoal_tac "f (Suc n) \<in> A")
  apply simp
  apply (thin_tac "f (Suc n) \<notin> A")
 apply (rule ideal_ele_sumTr2, assumption+)
  apply simp
  apply (subgoal_tac "nsum0 R f n \<in> carrier R")
  apply simp
  apply (simp add:nsum_mem Nset_def)
  apply assumption
 apply (simp add:nsum_ideal_inc)
  apply (simp add:Nset_def)
  apply (rule equalityI)
   apply (rule subsetI) apply (simp add:CollectI)
   apply (erule conjE) apply (frule le_imp_less_or_eq)
    apply (thin_tac "x \<le> Suc n") apply simp
   apply (rule subsetI) apply (simp add:CollectI)
 apply (simp add:Nset_def)
 apply (subgoal_tac "j \<in> Nset n")
 apply simp
 apply (rule contrapos_pp) apply simp+ 
 apply (subgoal_tac "nsum0 R f n \<notin> A")
 apply (subgoal_tac "nsum0 R f n \<in> A") apply simp
  apply (thin_tac "nsum0 R f n \<notin> A")
 apply (rule ideal_ele_sumTr1, assumption+)
  apply (subgoal_tac "f (Suc n) \<in> carrier R")
  apply simp apply (simp add:Nset_def)
  apply (simp add:nsum_mem Nset_def)
  apply assumption
 apply (subgoal_tac "Suc n \<in> Nset (Suc n) - {j}")
  apply simp
  apply (subgoal_tac "j \<noteq> Suc n")
  apply (simp add:Nset_def CollectI)
  apply assumption
   apply (subgoal_tac "\<forall>k. k\<in> Nset n \<longrightarrow> k \<in> Nset (Suc n)")
  apply blast apply (simp add:Nset_def)
 apply (thin_tac "(\<forall>i\<in>Nset n. f i \<in> carrier R) \<and>
 (\<exists>j\<in>Nset n. (\<forall>l\<in>Nset n - {j}. f l \<in> A) \<and> f j \<notin> A) \<longrightarrow> nsum0 R f n \<notin> A")
 apply (thin_tac "\<forall>i\<in>Nset (Suc n). f i \<in> carrier R")
 apply (thin_tac "\<forall>l\<in>Nset (Suc n) - {j}. f l \<in> A")
 apply (simp add:Nset_def)
done

lemma nsum_ideal_exc:"\<lbrakk>ring R; ideal R A; \<forall>i\<in>Nset n. f i \<in> carrier R; \<exists>j\<in>Nset n. (\<forall>l\<in>Nset n -{j}. f l \<in> A) \<and> (f j \<notin> A) \<rbrakk> \<Longrightarrow> nsum0 R f n \<notin> A"
apply (simp add:nsum_ideal_excTr)
done

lemma nprod_memTr:"ring R \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> carrier R) \<longrightarrow> (\<forall>l. l \<le> n \<longrightarrow>
   nprod0 R f l \<in> carrier R)"
apply (induct_tac n)
apply (rule impI)
apply (rule allI)
apply (rule impI)
 apply (simp add:Nset_def)
apply (rule impI)
 apply (rule allI)
 apply (rule impI)
apply (case_tac "l \<le> n")
 apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in> Nset (Suc n)")
 apply blast
 apply (simp add:Nset_def)
apply (subgoal_tac "l = Suc n")
 apply (thin_tac "l \<le> Suc n")
 apply (thin_tac " \<not> l \<le> n")
 apply simp
 apply (rule ring_tOp_closed, assumption+)
 apply (simp add:Nset_def)
 apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in> Nset (Suc n)")
 apply blast apply (simp add:Nset_def)
apply simp
done

lemma nprod_mem:"\<lbrakk>ring R; \<forall>i\<in>Nset n. f i \<in> carrier R; l \<le> n \<rbrakk> \<Longrightarrow>
   nprod0 R f l \<in> carrier R"
apply (simp add:nprod_memTr)
done

lemma nprod_incTr:"\<lbrakk>ring R; ideal R A\<rbrakk> \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> carrier R) \<and> (\<exists>l\<in>Nset n. f l \<in> A) \<longrightarrow> nprod0 R f n \<in> A"
apply (induct_tac n)  
(** n = 0 **)
apply (simp add:Nset_def)
apply (rule impI)
 apply (erule conjE)+ 
 (** n = 0 OK **) 
(** n **)
apply simp
 apply (subgoal_tac "\<forall>l\<in>Nset (Suc n). f l \<in> A \<longrightarrow>  f (Suc n) \<cdot>\<^sub>R (nprod0 R f n) \<in> A")
 apply blast apply (thin_tac "\<exists>l\<in>Nset (Suc n). f l \<in> A")
 apply (rule ballI) apply (rule impI)
apply (case_tac "l \<in> Nset n")
 apply (subgoal_tac "nprod0 R f n \<in> A")
 apply (rule ideal_ring_multiple, assumption+)
 apply (simp add:Nset_def)
 apply (subgoal_tac "\<forall>l. l\<in>Nset n \<longrightarrow> l \<in> Nset (Suc n)")
 apply blast
 apply (simp add:Nset_def)
 
 apply (thin_tac "(\<forall>i\<in>Nset n. f i \<in> carrier R) \<and> (\<exists>l\<in>Nset n. f l \<in> A) \<longrightarrow>
             nprod0 R f n \<in> A")
 apply (subgoal_tac "l = Suc n")
 apply simp
 apply (rule ideal_ring_multiple1, assumption+)
 apply (subgoal_tac "\<forall>k. k\<in>Nset n \<longrightarrow> k \<in> Nset (Suc n)")
 apply (simp add:nprod_mem) apply (simp add:Nset_def)
  apply (thin_tac "\<forall>i\<in>Nset (Suc n). f i \<in> carrier R")
  apply (thin_tac "f l \<in> A")
 apply (simp add:Nset_def)
done

lemma ideal_nprod_inc:"\<lbrakk>ring R; ideal R A; \<forall>i\<in>Nset n. f i \<in> carrier R; \<exists>l\<in>Nset n. f l \<in> A\<rbrakk> \<Longrightarrow> nprod0 R f n \<in> A"
apply (simp add:nprod_incTr)
done

lemma nprod_excTr:"\<lbrakk>ring R; prime_ideal R P\<rbrakk> \<Longrightarrow> (\<forall>i\<in>Nset n. f i \<in> carrier R) \<and> (\<forall>l\<in>Nset n. f l \<notin> P) \<longrightarrow> nprod0 R f n \<notin> P"
apply (induct_tac n)
(** n = 0 **)
 apply (simp add:Nset_def) (* n = 0 done *)
(** n **)
apply (rule impI)
apply (erule conjE)+
 apply simp
 apply (subgoal_tac "f (Suc n) \<in> carrier R")
 apply (subgoal_tac "nprod0 R f n \<in> carrier R")
 apply (subgoal_tac "f (Suc n) \<notin> P")
 apply (subgoal_tac " nprod0 R f n \<notin> P")
  apply (thin_tac "(\<forall>i\<in>Nset n. f i \<in> carrier R) \<and> (\<forall>l\<in>Nset n. f l \<notin> P) \<longrightarrow>
           nprod0 R f n \<notin> P")
 apply (rule contrapos_pp) apply simp+
 apply (simp add:prime_ideal_def)
 apply (erule conjE)+
 apply (subgoal_tac "f (Suc n) \<in> P \<or> nprod0 R f n \<in> P")
  apply (thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P")
 apply simp
  apply (thin_tac "f (Suc n) \<notin> P")
  apply (thin_tac "nprod0 R f n \<notin> P")
 apply simp
 apply (subgoal_tac "\<forall>k. k \<in> Nset n \<longrightarrow> k \<in> Nset (Suc n)")
  apply simp apply (simp add:Nset_def)
 apply (simp add:Nset_def)
  apply (subgoal_tac "n \<le> Suc n")
 apply (frule nprod_mem, assumption+)
  apply simp
 apply (simp add:Nset_def)
done

lemma prime_nprod_exc:"\<lbrakk>ring R; prime_ideal R P; \<forall>i\<in>Nset n. f i \<in> carrier R;
\<forall>l\<in>Nset n. f l \<notin> P\<rbrakk> \<Longrightarrow> nprod0 R f n \<notin> P"
apply (simp add:nprod_excTr)
done

constdefs
 nilrad::"('a, 'more) RingType_scheme \<Rightarrow> 'a set"
  "nilrad R == {x. x \<in> carrier R \<and> nilpotent R x}" 

lemma id_nilrad_ideal:"ring R \<Longrightarrow> ideal R (nilrad R)"
apply (frule ring_is_ag)
apply (rule ideal_condition [of "R" "nilrad R"], assumption+)
apply (rule subsetI) apply (simp add:nilrad_def CollectI)
apply (simp add:nilrad_def) 
 apply (subgoal_tac "0\<^sub>R \<in> carrier R")
 apply (subgoal_tac "nilpotent R (0\<^sub>R)")
 apply blast
 apply (simp add:nilpotent_def)
 apply (subgoal_tac "(0\<^sub>R)^\<^sup>R\<^sup> \<^sup>1 = 0\<^sub>R") 
 apply (subgoal_tac "1 \<in> NSet")
 apply blast
 apply (simp add:NSet_def)
 apply simp
apply (rule ring_times_0_x, assumption+)  
 apply (simp add:ring_def) apply (simp add:ring_def agroup_def)
apply (rule ballI)+
apply (subgoal_tac "-\<^sub>R y \<in> nilrad R")
apply (simp add:nilrad_def CollectI)
apply (rule conjI) apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier R \<and> nilpotent R x")
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "y \<in> carrier R \<and> nilpotent R y") 
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "-\<^sub>R y \<in> carrier R \<and> nilpotent R (-\<^sub>R y)")
 apply (simp add:ag_pOp_closed)

 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier R \<and> nilpotent R x")
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "y \<in> carrier R \<and> nilpotent R y") 
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "-\<^sub>R y \<in> carrier R \<and> nilpotent R (-\<^sub>R y)")
apply (simp add:nilpotent_def)
apply auto (* thm npAdd *)
apply (subgoal_tac "( x +\<^sub>R -\<^sub>R y)^\<^sup>R\<^sup> \<^sup>(n + nb) = 0\<^sub>R") 
apply (subgoal_tac "n + nb \<in> NSet") apply blast apply (simp add:NSet_def)
apply (rule npAdd, assumption+)

apply (simp add:nilrad_def CollectI)
apply (rule conjI) apply (simp add:ag_mOp_closed) (* thm npInverse *)
 apply (thin_tac "x \<in> carrier R \<and> nilpotent R x")
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "y \<in> carrier R \<and> nilpotent R y")
 apply (simp add:nilpotent_def)
apply auto 
apply (subgoal_tac "(-\<^sub>R y)^\<^sup>R\<^sup> \<^sup>n = y^\<^sup>R\<^sup> \<^sup>n \<or> (-\<^sub>R y)^\<^sup>R\<^sup> \<^sup>n = -\<^sub>R y^\<^sup>R\<^sup> \<^sup>n")
apply (simp add:ag_inv_zero)
apply blast 
apply (rule npInverse, assumption+)

apply (simp add:nilrad_def CollectI)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier R \<and> nilpotent R x")
apply (rule conjI)
apply (simp add:ring_tOp_closed)
apply (simp add:nilpotent_def CollectI)
apply auto

apply (subgoal_tac "(r \<cdot>\<^sub>R x)^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R") apply blast
apply (simp add: npMul) apply (rule ring_times_x_0, assumption) 
apply (simp add:npClose)
done

constdefs
 rad_ideal :: "['a RingType, 'a set ] \<Rightarrow> 'a set"
  "rad_ideal R I == {a. a \<in> carrier R \<and> nilpotent (qring R I) ((pj R I) a)}"

lemma id_rad_invim:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> 
   rad_ideal R I = (rInvim R (qring R I) (pj R I ) (nilrad (qring R I)))"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:rad_ideal_def)
 apply (frule conj_1) apply (frule conj_2) 
  apply (thin_tac "x \<in> carrier R \<and> nilpotent (qring R I) ((pj R I ) x)")
 apply (simp add:rInvim_def)
 apply (simp add:nilrad_def)
 apply (subst  pj_mem, assumption+)
 apply (simp add:qring_def ar_coset_def set_r_cos_def) 
 apply (subgoal_tac "carrier (b_ag R) = carrier R") apply simp
 apply blast apply (simp add:b_ag_def)

apply (rule subsetI)
 apply (simp add:rInvim_def nilrad_def) 
apply (simp add: rad_ideal_def)
done 

lemma id_rad_ideal:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> ideal R (rad_ideal R I)"
(* thm invim_of_ideal *)
apply (subst id_rad_invim [of "R" "I"], assumption+)
apply (rule invim_of_ideal, assumption+)
apply (rule id_nilrad_ideal) 
apply (simp add:qring_ring)
done

lemma id_rad_cont_I:"\<lbrakk> ring R; ideal R I \<rbrakk> \<Longrightarrow> I \<subseteq> (rad_ideal R I)"
apply (simp add:rad_ideal_def)
apply (rule subsetI) apply (simp add:CollectI)
apply (simp add:ideal_subset)
apply (simp add:nilpotent_def)
apply (subst pj_mem, assumption+)
apply (simp add:ideal_subset) (* thm npQring *)
apply (subgoal_tac "(x \<uplus>\<^sub>R I)^\<^sup>(qring R I)\<^sup> \<^sup>1 = 0\<^sub>(qring R I)")
apply (subgoal_tac "1 \<in> NSet") 
apply blast
apply (simp add:NSet_def)
apply simp

apply (frule ideal_subset, assumption+)
apply (subgoal_tac "1\<^sub>qring R I = 1\<^sub>R \<uplus>\<^sub>R I") apply simp
apply (subgoal_tac "0\<^sub>(qring R I) = I") apply simp
apply (rule trans)
apply (rule  qring_tOp [of "R" "I" _ "1\<^sub>R"], assumption+)
 apply (simp add:ring_def) 
 apply (simp add:ring_r_one ar_coset_def) (* thm r_cosUnit1_1 *)
 apply (rule r_cosUnit1_1 [of "b_ag R" "I" _])
 apply (rule b_ag_group) apply (simp add:ring_def)
 apply (simp add:ideal_def asubgroup_def)
 apply (simp add:ideal_subset) apply (simp add:qring_def)
 apply (simp add:qring_def)
done

lemma id_rad_set:"\<lbrakk>ring R; ideal R I\<rbrakk> \<Longrightarrow>
      rad_ideal R I = {x. x \<in> carrier R \<and> (\<exists>n. npow R x n \<in> I)}"
apply auto
apply (simp add:rad_ideal_def)
apply (simp add:rad_ideal_def)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<in> carrier R \<and> nilpotent (qring R I) ((pj R I) x)")
apply (simp add:nilpotent_def)

apply (simp add: pj_mem)
apply (simp add:npQring)
apply (subgoal_tac "0\<^sub>(qring R I) = I")
apply simp  (* thm ar_coset_same3 *)
apply (subgoal_tac "\<forall>n\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n \<uplus>\<^sub>R I = I \<longrightarrow> x^\<^sup>R\<^sup> \<^sup>n \<in> I")
apply blast apply (thin_tac "\<exists>n\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n \<uplus>\<^sub>R I = I")
apply (rule ballI) apply (rule impI)
apply (rule ar_coset_same3, assumption+) 
apply (simp add:npClose) apply assumption apply (simp add:qring_def)
apply (simp add:rad_ideal_def)
apply (simp add:nilpotent_def)
apply (subst pj_mem, assumption+) (* thm npQring *)
apply (simp add:npQring)
apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>n \<uplus>\<^sub>R I = I") 
apply (simp add:qring_def) apply (subgoal_tac "n \<in> NSet")
apply blast apply (simp add:NSet_def)
apply (rule ar_coset_same4, assumption+)
apply (simp add:npClose)
apply assumption
done

lemma rad_primary_prime:"\<lbrakk>ring R; primary_ideal R q \<rbrakk>
       \<Longrightarrow> prime_ideal R (rad_ideal R q)" 
apply (simp add:prime_ideal_def)
apply (rule conjI) apply (rule id_rad_ideal, assumption+)
apply (simp add:primary_ideal_def)
apply (rule conjI)
apply (simp add:rad_ideal_def primary_ideal_def)
apply (subgoal_tac "1\<^sub>R \<in> carrier R") apply simp
apply (simp add:nilpotent_def)
apply (rule ballI)
apply (subgoal_tac "((pj R q) (1\<^sub>R))^\<^sup>(qring R q)\<^sup> \<^sup>n = (pj R q) (1\<^sub>R)") 
apply simp  
apply (subst pj_mem, assumption+) apply simp apply (simp add:ring_def)
apply (simp add:qring_def) apply (fold qring_def) 
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "ideal R q \<and> 1\<^sub>R \<notin> q \<and> (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. 
             x \<cdot>\<^sub>R y \<in> q \<longrightarrow> (\<exists>n. x^\<^sup>R\<^sup> \<^sup>n \<in> q) \<or> y \<in> q)")
 apply (frule conj_1)
 apply (thin_tac "1\<^sub>R \<notin> q \<and> (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. 
                            x \<cdot>\<^sub>R y \<in> q \<longrightarrow> (\<exists>n. x^\<^sup>R\<^sup> \<^sup>n \<in> q) \<or> y \<in> q)")
 apply (thin_tac "(pj R q) (1\<^sub>R)^\<^sup>(qring R q)\<^sup> \<^sup>n = (pj R q) (1\<^sub>R)")
 apply (rule contrapos_pp) apply simp+
 apply (subgoal_tac "1\<^sub>R \<in> q") apply simp
 apply (subgoal_tac "1\<^sub>R \<in>  1\<^sub>R \<uplus>\<^sub>R q") apply simp
  apply (thin_tac "1\<^sub>R \<uplus>\<^sub>R q = q") apply (thin_tac "1\<^sub>R \<notin> q")
 apply (simp add:ar_coset_def)
apply (rule aInR_cos) apply (rule b_ag_group) apply (simp add:ring_def)
 apply (simp add:ideal_def asubgroup_def)
 apply (simp add:b_ag_def ring_def)  
 apply (subst pj_mem, assumption+) apply (simp add:primary_ideal_def)
 apply (simp add:ring_def)
apply (subst npQring, assumption+) apply (simp add:primary_ideal_def)
 apply (simp add:ring_def)
 apply (simp add:npOne) apply (simp add:ring_def)

apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (case_tac "x \<in> rad_ideal R q ") apply simp apply simp
apply (subst id_rad_set, assumption+)
apply (simp add:rad_ideal_def) apply (simp add:primary_ideal_def)
apply (simp add:primary_ideal_def)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "ideal R q \<and> 1\<^sub>R \<notin> q \<and>
             (\<forall>x\<in>carrier R.
                 \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> q \<longrightarrow> (\<exists>n. x^\<^sup>R\<^sup> \<^sup>n \<in> q) \<or> y \<in> q)")
apply (frule id_rad_set, assumption) apply (rotate_tac 7)
 apply simp
 apply (thin_tac "rad_ideal R q = {x. x \<in> carrier R \<and> (\<exists>n. x^\<^sup>R\<^sup> \<^sup>n \<in> q)}")
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "x \<cdot>\<^sub>R y \<in> carrier R \<and> (\<exists>n. ( x \<cdot>\<^sub>R y)^\<^sup>R\<^sup> \<^sup>n \<in> q)")
apply (simp add:npMul)
apply (subgoal_tac "\<forall>n. x^\<^sup>R\<^sup> \<^sup>n \<cdot>\<^sub>R y^\<^sup>R\<^sup> \<^sup>n \<in> q \<longrightarrow>  (\<exists>n. y^\<^sup>R\<^sup> \<^sup>n \<in> q)")
apply blast apply (thin_tac "\<exists>n.  x^\<^sup>R\<^sup> \<^sup>n \<cdot>\<^sub>R y^\<^sup>R\<^sup> \<^sup>n \<in> q")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "\<exists>m. (npow R (npow R x n) m) \<in> q \<or> (npow R y n) \<in> q")
apply (subgoal_tac "\<forall>m. x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>m \<in> q \<or> y^\<^sup>R\<^sup> \<^sup>n \<in> q \<longrightarrow> (\<exists>n. y^\<^sup>R\<^sup> \<^sup>n \<in> q)")
apply blast apply (rule allI) apply (rule impI)
(* thm npMulExp [of "R" _] *)
 apply (thin_tac "\<exists>m. x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>m \<in> q \<or> y^\<^sup>R\<^sup> \<^sup>n \<in> q")
apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>m = npow R x (n*m)")
apply simp apply blast
apply (simp add:npMulExp [of "R" _ ])
apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>n \<in> carrier R")
apply (subgoal_tac "y^\<^sup>R\<^sup> \<^sup>n \<in> carrier R")
apply simp apply (simp add:npClose)+
done

lemma npow_notin_prime:"\<lbrakk>ring R; prime_ideal R P; x \<in> carrier R; x \<notin> P \<rbrakk>
                                \<Longrightarrow> \<forall>n. npow R x n \<notin> P" 
apply (rule allI) 
apply (induct_tac n)
apply simp 
apply (simp add:prime_ideal_def)
apply (simp add:ring_r_one)
apply (simp add:prime_ideal_def)
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "x \<cdot>\<^sub>R x^\<^sup>R\<^sup> \<^sup>na \<in> carrier R")
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac " ideal R P \<and> 1\<^sub>R \<notin> P \<and>
            (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P)")
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "1\<^sub>R \<notin> P \<and>
            (\<forall>x\<in>carrier R. \<forall>y\<in>carrier R.  x \<cdot>\<^sub>R y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P)")
apply (subgoal_tac "x^\<^sup>R\<^sup> \<^sup>na \<in> carrier R")
apply blast apply (simp add:npClose)
apply (rule ring_tOp_closed, assumption+)
apply (simp add:npClose)
done

lemma npow_in_prime:"\<lbrakk>ring R; prime_ideal R P; x \<in> carrier R; \<exists>n. npow R x n \<in> P \<rbrakk> \<Longrightarrow> x \<in> P"
apply (rule contrapos_pp) apply simp+
apply (frule npow_notin_prime, assumption+)
apply blast
done
       
constdefs
 mul_closed_set::"[('a, 'more) RingType_scheme, 'a set ] \<Rightarrow> bool"
 "mul_closed_set R S == S \<subseteq> carrier R \<and> (\<forall>s\<in>S. \<forall>t\<in>S. s \<cdot>\<^sub>R t \<in> S)"

 integral_domain::"('a, 'm) RingType_scheme \<Rightarrow> bool"
    "integral_domain R == ring R \<and> (\<forall>x\<in> carrier R. \<forall>y\<in> carrier R. x \<cdot>\<^sub>R y
     = 0\<^sub>R  \<longrightarrow> x = 0\<^sub>R \<or> y = 0\<^sub>R)"

record 'a FieldType = "'a RingType" + 
   iOp :: "'a \<Rightarrow> 'a"

constdefs
  field :: "('a, 'm) FieldType_scheme \<Rightarrow> bool"
  "field K == ring K \<and>
             (iOp K) \<in> (carrier K - {0\<^sub>K}) \<rightarrow> (carrier K - {0\<^sub>K}) \<and>
        (\<forall>x\<in>(carrier K - {0\<^sub>K}). (iOp K x) \<cdot>\<^sub>K x = 1\<^sub>K)"

  npowf   ::  "('a, 'more) FieldType_scheme  => 'a => int  => 'a"
  "npowf K x n == 
        if 0 \<le> n then npow K x (nat n) else npow K (iOp K x) (nat (- n))"
  
syntax
  "@NPOWF" ::  "['a, ('a, 'more) FieldType_scheme, int] \<Rightarrow>  'a" 
       ("(3_\<^sub>_\<^sup>_)" [77,77,78]77)
 
  "@IOP"   :: "['a, ('a, 'more) FieldType_scheme] \<Rightarrow> 'a"
       ("(_\<^sup>\<hyphen>\<^sup>_)" [87,88]87) 
  
translations
  "a\<^sub>K\<^sup>n" == "npowf K a n " 
  "a\<^sup>\<hyphen>\<^sup>K" == "FieldType.iOp K a"

lemma idom_is_ring:"integral_domain R \<Longrightarrow> ring R"
apply (simp add:integral_domain_def)
done

lemma idom_tOp_nonzeros:"\<lbrakk>integral_domain R; x \<in> carrier R; y \<in> carrier R; 
x \<noteq> 0\<^sub>R;  y \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow> x \<cdot>\<^sub>R y \<noteq> 0\<^sub>R"
apply (rule contrapos_pp, simp+)
apply (simp add:integral_domain_def) apply (erule conjE)+
 apply (subgoal_tac "x = 0\<^sub>R \<or> y = 0\<^sub>R")
 apply simp 
 apply (thin_tac "x \<noteq> 0\<^sub>R") apply (thin_tac "y \<noteq> 0\<^sub>R")
 apply simp
done

lemma idom_potent_nonzero:"\<lbrakk>integral_domain R; x \<in> carrier R; x \<noteq> 0\<^sub>R\<rbrakk>
                             \<Longrightarrow> npow R x n \<noteq> 0\<^sub>R" 
apply (induct_tac n)
 apply simp  (* case 0 *)
 apply (rule contrapos_pp, simp+)
 apply (frule idom_is_ring[of"R"]) 
 apply (frule ring_l_one[of "R" "x", THEN sym], assumption+) apply simp
 apply (simp add:ring_times_0_x)
 (* case (Suc n) *)
 apply (rule contrapos_pp, simp+)
 apply (simp add:integral_domain_def) apply (erule conjE)
 apply (subgoal_tac "x = 0\<^sub>R \<or> x^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R")
 apply blast apply (thin_tac "x \<noteq> 0\<^sub>R") apply (thin_tac "x^\<^sup>R\<^sup> \<^sup>n \<noteq> 0\<^sub>R")
 apply (frule_tac n = n in npClose[of "R" "x"], assumption+)
 apply simp
done

lemma idom_potent_unit:"\<lbrakk>integral_domain R; a \<in> carrier R; 0 < n\<rbrakk>
                 \<Longrightarrow> (unit R a) = (unit R (npow R a n))" 
apply (frule idom_is_ring[of "R"])
apply (rule iffI)
apply (simp add:unit_def)
 apply (subgoal_tac "\<forall>y\<in>carrier R. RingType.tOp R a y = RingType.one R
 \<longrightarrow> (\<exists>y\<in>carrier R. RingType.tOp R (a^\<^sup>R\<^sup> \<^sup>n) y = RingType.one R)")
 apply blast apply (thin_tac " \<exists>y\<in>carrier R. RingType.tOp R a y = 1\<^sub>R")
 apply (rule ballI) apply (rule impI)
 apply (frule idom_is_ring[of "R"])
 apply (frule_tac y = y in npMul[of "R" "a" _ "n"], assumption+)
 apply simp apply (simp add:npOne)
 apply (frule_tac x = y and n = n in npClose[of "R"], assumption+)
 apply blast
apply (simp add:unit_def)
 apply (subgoal_tac "\<forall>y\<in>carrier R. RingType.tOp R (a^\<^sup>R\<^sup> \<^sup>n) y = 1\<^sub>R \<longrightarrow>
       (\<exists>y\<in>carrier R. RingType.tOp R a y = RingType.one R)")
 apply blast apply (thin_tac "\<exists>y\<in>carrier R. RingType.tOp R (a^\<^sup>R\<^sup> \<^sup>n) y = 1\<^sub>R")
 apply (rule ballI)
 apply (rule impI)
 apply (subgoal_tac "a^\<^sup>R\<^sup> \<^sup>n = a^\<^sup>R\<^sup> \<^sup>(Suc (n - Suc 0))")
 apply (simp del:Suc_pred)
 apply (thin_tac "a^\<^sup>R\<^sup> \<^sup>n = RingType.tOp R a (a^\<^sup>R\<^sup> \<^sup>(n - Suc 0))")
 apply (frule_tac n = "n - Suc 0" in npClose[of "R" "a"], assumption+)
 apply (simp add:ring_tOp_assoc[of "R" "a"])
 apply (frule_tac y = y in ring_tOp_closed[of "R" "a^\<^sup>R\<^sup> \<^sup>(n - Suc 0)"],
                                     assumption+)
 apply blast
 apply simp
done

lemma idom_mult_cancel_r:"\<lbrakk>integral_domain R; a \<in> carrier R; b \<in> carrier R;
 c \<in> carrier R; c \<noteq> 0\<^sub>R; a \<cdot>\<^sub>R c = b \<cdot>\<^sub>R c\<rbrakk> \<Longrightarrow> a = b"
apply (frule idom_is_ring[of "R"]) 
apply (frule ring_is_ag[of "R"])
 apply (frule ring_tOp_closed[of "R" "a" "c"], assumption+)
 apply (frule ring_tOp_closed[of "R" "b" "c"], assumption+)
 apply (simp add:ag_eq_diffzero[of "R" "a \<cdot>\<^sub>R c" "b \<cdot>\<^sub>R c"])
 apply (simp add:ring_inv1_1)
 apply (frule ag_mOp_closed[of "R" "b"], assumption+)
 apply (simp add:ring_distrib2[THEN sym, of "R" "c" "a" "-\<^sub>R b"])
 apply (frule ag_pOp_closed[of "R" "a" "-\<^sub>R b"], assumption+)
 apply (simp add:integral_domain_def)
 apply (subgoal_tac "( a +\<^sub>R -\<^sub>R b) = 0\<^sub>R \<or> c = 0\<^sub>R")
  prefer 2 apply blast
apply (thin_tac "\<forall>x\<in>carrier R. \<forall>y\<in>carrier R. RingType.tOp R x y = 0\<^sub>R \<longrightarrow> x = 0\<^sub>R \<or> y = 0\<^sub>R")
 apply simp
 apply (simp add:ag_eq_diffzero[THEN sym])
done

lemma idom_mult_cancel_l:"\<lbrakk>integral_domain R; a \<in> carrier R; b \<in> carrier R;
 c \<in> carrier R; c \<noteq> 0\<^sub>R; c \<cdot>\<^sub>R a = c \<cdot>\<^sub>R b\<rbrakk> \<Longrightarrow> a = b"
apply (frule idom_is_ring[of "R"])
apply (simp add:ring_tOp_commute)
apply (simp add:idom_mult_cancel_r)
done

lemma field_iOp_closed:"\<lbrakk>field K; x \<in> carrier K - {0\<^sub>K}\<rbrakk> \<Longrightarrow>
                               iOp K x \<in> (carrier K) - {0\<^sub>K}"
apply (simp add:field_def) apply (erule conjE)+
 apply (subgoal_tac "x \<in> carrier K - {0\<^sub>K}")
 apply (frule funcset_mem [of "FieldType.iOp K" "carrier K - {0\<^sub>K}" "carrier K - {0\<^sub>K}" "x"], assumption+)  apply simp apply simp
done 

lemma field_iOp:"\<lbrakk>field K; x \<in> carrier K - {0\<^sub>K}\<rbrakk> \<Longrightarrow> (iOp K x) \<cdot>\<^sub>K x = 1\<^sub>K"
apply (simp add:field_def)
done

lemma field_is_ring:"field K \<Longrightarrow> ring K"
 apply (simp add:field_def)
done

lemma field_inv_one:"\<lbrakk>field K; 1\<^sub>K \<noteq> 0\<^sub>K\<rbrakk>  \<Longrightarrow> iOp K (1\<^sub>K) = 1\<^sub>K"
apply (frule field_is_ring[of "K"])
 apply (frule ring_one[of "K"])
 apply (frule field_iOp [of "K" "1\<^sub>K"])
 apply simp
 apply (frule field_iOp_closed [of "K" "1\<^sub>K"])
 apply simp
 apply (simp add:ring_r_one)
done

lemma field_tOp_assoc:"\<lbrakk>field K; x \<in> carrier K; y \<in> carrier K; z \<in> carrier K\<rbrakk>
                                \<Longrightarrow> x \<cdot>\<^sub>K y \<cdot>\<^sub>K z =  x \<cdot>\<^sub>K (y \<cdot>\<^sub>K z)"  
apply (frule field_is_ring [of "K"])
apply (simp add:ring_tOp_assoc)
done

lemma field_inv_inv:"\<lbrakk>field K; x \<in> carrier K; x \<noteq> 0\<^sub>K\<rbrakk> \<Longrightarrow> (x\<^sup>\<hyphen>\<^sup>K)\<^sup>\<hyphen>\<^sup>K = x"
apply (frule field_iOp_closed[of "K" "x"]) apply simp
 apply (frule field_iOp[of "K" "x\<^sup>\<hyphen>\<^sup>K"], assumption+)
 apply simp 
 apply (frule field_is_ring[of "K"])
 apply (subgoal_tac "(x\<^sup>\<hyphen>\<^sup>K\<^sup>\<hyphen>\<^sup>K) \<cdot>\<^sub>K (x\<^sup>\<hyphen>\<^sup>K) \<cdot>\<^sub>K x = 1\<^sub>K \<cdot>\<^sub>K x") prefer 2 apply simp
 apply (thin_tac "RingType.tOp K (x\<^sup>\<hyphen>\<^sup>K\<^sup>\<hyphen>\<^sup>K) (x\<^sup>\<hyphen>\<^sup>K) = RingType.one K")
 apply (erule conjE)
 apply (frule field_iOp_closed[of "K" "x\<^sup>\<hyphen>\<^sup>K"]) apply simp apply simp
 apply (erule conjE)+
 apply (simp add:ring_tOp_assoc)
 apply (simp add:field_iOp) apply (simp add:ring_r_one)
 apply (simp add:ring_l_one)
done

lemma field_is_idom:"field K \<Longrightarrow> integral_domain K" 
apply (simp add:integral_domain_def)
 apply (frule field_is_ring[of "K"]) apply simp
 apply (rule ballI)+ apply (rule impI)
 apply (rule contrapos_pp, simp+) apply (erule conjE)
apply (frule_tac x = x in field_iOp_closed [of "K"]) apply simp
apply simp apply (erule conjE)
apply (subgoal_tac "(iOp K x) \<cdot>\<^sub>K (x \<cdot>\<^sub>K y) = (iOp K x) \<cdot>\<^sub>K 0\<^sub>K")
 apply (thin_tac "RingType.tOp K x y = 0\<^sub>K")
 apply (frule field_is_ring[of "K"])
 apply (simp add:ring_times_x_0)
apply (simp add:field_tOp_assoc[THEN sym])
 apply (simp add:field_iOp)
 apply (simp add:ring_l_one)
apply simp
done

lemma field_potent_nonzero:"\<lbrakk>field K; x \<in> carrier K; x \<noteq> 0\<^sub>K\<rbrakk> \<Longrightarrow>  x^\<^sup>K\<^sup> \<^sup>n \<noteq> 0\<^sub>K"
apply (frule field_is_idom[of "K"])
 apply (simp add:idom_potent_nonzero)
done

lemma field_nilp_zero:"\<lbrakk>field K; x \<in> carrier K; x^\<^sup>K\<^sup> \<^sup>n = 0\<^sub>K\<rbrakk> \<Longrightarrow> x = 0\<^sub>K"
apply (rule contrapos_pp, simp+) 
 apply (simp add:field_potent_nonzero)
done

lemma npowf_mem:"\<lbrakk>field K; a \<in> carrier K; a \<noteq> 0\<^sub>K\<rbrakk> \<Longrightarrow> 
                                    npowf K a n \<in> carrier K"
apply (simp add:npowf_def)
apply (case_tac "0 \<le> n") apply simp
 apply (frule field_is_ring[of "K"])
 apply (simp add:npClose)
 apply simp
 apply (frule field_is_ring[of "K"])
 apply (frule field_iOp_closed[of "K" "a"]) apply simp
 apply (frule npClose [of "K" "a\<^sup>\<hyphen>\<^sup>K" "nat (-n)"])
 apply simp apply assumption
done
 
lemma residue_fieldTr:"\<lbrakk> ring R; maximal_ideal R mx; x \<in> carrier(qring R mx); 
 x \<noteq> 0\<^sub>(qring R mx)\<rbrakk> \<Longrightarrow>\<exists>y\<in>carrier (qring R mx). x \<cdot>\<^sub>(qring R mx) y = 1\<^sub>(qring R mx)"
apply (simp add:maximal_ideal_def)
apply (subgoal_tac "(\<exists>a\<in>carrier (b_ag R). x = r_coset (b_ag R) mx a)\<and>x \<noteq> mx")
prefer 2 apply (simp add:qring_def set_r_cos_def)  
apply (subgoal_tac "\<forall>a\<in>carrier (b_ag R). (x = mx\<^sub>(b_ag R) a \<and> x \<noteq> mx)  \<longrightarrow>
  (\<exists>y\<in>carrier (R /\<^sub>r mx). RingType.tOp (R /\<^sub>r mx) x y = RingType.one (R /\<^sub>r mx))")
apply blast apply (thin_tac "(\<exists>a\<in>carrier (b_ag R). x = mx\<^sub>(b_ag R) a) \<and> x \<noteq> mx")
apply (rule ballI) apply (rule impI)
apply (subgoal_tac "a \<notin> mx")
apply (subgoal_tac "mx \<^bold>+\<^sub>R (R \<diamondsuit> a) = carrier R")
apply (frule ring_one [of "R"]) apply (frule sym) 
 apply (thin_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> a = carrier R") apply simp
 apply (thin_tac "carrier R = mx \<^bold>+\<^sub>R R \<diamondsuit> a")
 apply (simp add:asettOp_def settOp_def)
apply (subgoal_tac "\<forall>x\<in>mx. \<forall>y\<in>R \<diamondsuit> a. GroupType.tOp (b_ag R) x y = RingType.one R \<longrightarrow> (\<exists>y\<in>carrier (R /\<^sub>r mx). RingType.tOp (R /\<^sub>r mx) (mx\<^sub>(b_ag R) a) y = RingType.one (R /\<^sub>r mx))")
apply blast apply (erule conjE)+
 apply (thin_tac "x = mx\<^sub>(b_ag R) a")
 apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} =
           {mx, {z. \<exists>x\<in>mx. \<exists>y\<in>R \<diamondsuit> a. GroupType.tOp (b_ag R) x y = z}}")
apply (thin_tac "\<exists>x\<in>mx.\<exists>y\<in>R \<diamondsuit> a. GroupType.tOp (b_ag R) x y = RingType.one R")
apply (rule ballI)+ apply (rule impI)
apply (simp add:Rxa_def)
apply (subgoal_tac "\<forall>r\<in>carrier R. y =  r \<cdot>\<^sub>R a \<longrightarrow> (\<exists>y\<in>carrier (R /\<^sub>r mx). RingType.tOp (R /\<^sub>r mx) (mx\<^sub>(b_ag R) a) y = RingType.one (R /\<^sub>r mx))") apply blast
apply (thin_tac "\<exists>r\<in>carrier R. y = RingType.tOp R r a")
apply (rule ballI) apply (rule impI) apply simp
 apply (subgoal_tac "mx\<^sub>(b_ag R) a = a \<uplus>\<^sub>R mx") apply simp
 apply (thin_tac "mx\<^sub>(b_ag R) a = a \<uplus>\<^sub>R mx") apply (simp add:b_ag_def)
   prefer 2 apply (simp add:ar_coset_def)
 apply (subgoal_tac "(a \<uplus>\<^sub>R mx) \<cdot>\<^sub>(qring R mx) ( r \<uplus>\<^sub>R mx) = 1\<^sub>(qring R mx)")
 apply (frule_tac h = xa in ideal_subset [of "R" "mx"], assumption+)
 apply (frule_tac a =  r in qring_mem [of "R" "mx"], assumption+)
 apply blast
 apply (frule_tac h = xa in ideal_subset [of "R" "mx"], assumption+)
 apply (simp add:qring_tOp)
 apply (thin_tac "a \<uplus>\<^sub>R mx \<in> carrier (R /\<^sub>r mx)")
 apply (thin_tac "y = RingType.tOp R r a")
 apply (frule sym)
  apply (thin_tac "xa +\<^sub>R (RingType.tOp R r a) = RingType.one R")
  apply (simp add:ring_tOp_commute)
  apply (frule_tac x = a and y = r in ring_tOp_closed [of "R"], assumption+)
  apply (frule ring_is_ag[of "R"])
  apply (frule_tac x = xa and y = "a \<cdot>\<^sub>R r" in ag_pOp_commute, assumption+)
  apply simp 
  apply (thin_tac "xa +\<^sub>R ((RingType.tOp R) a r) = (RingType.tOp R a r) +\<^sub>R xa")
  apply (simp add:qring_def)
  apply (frule_tac a1 = "a \<cdot>\<^sub>R r" and b1 = xa in qring_pOp [THEN sym, of "R" "mx"], assumption+) apply simp apply (simp add:Qring_fix1)
  apply (thin_tac "(RingType.tOp R a r +\<^sub>R xa) \<uplus>\<^sub>R mx = (RingType.tOp R a r \<uplus>\<^sub>R mx) +\<^sub>(R /\<^sub>r mx) mx")
  apply (thin_tac "RingType.one R =  RingType.tOp R a r +\<^sub>R xa")
apply (frule_tac a =  "a \<cdot>\<^sub>R r" in qring_mem [of "R" "mx"], assumption+)  
 apply (frule qring_ring[of "R" "mx"], assumption+)
 apply (frule ring_is_ag [of "qring R mx"])
 apply (frule_tac t = "(a \<cdot>\<^sub>R r) \<uplus>\<^sub>R mx" in ag_r_zero [THEN sym, of "qring R mx"], assumption+) apply (simp add:qring_def)
 
 apply (subgoal_tac "mx\<^sub>(b_ag R) a = a \<uplus>\<^sub>R mx") apply simp
 apply (thin_tac "mx\<^sub>(b_ag R) a = a \<uplus>\<^sub>R mx") apply (simp add:b_ag_def)
 apply (erule conjE)+
 apply (frule_tac a = a in principal_ideal [of "R"], assumption+)
 apply (frule_tac ?I2.0 = "R \<diamondsuit> a" in sum_ideals [of "R" "mx"], assumption+)
 apply (frule_tac ?I2.0 = "R \<diamondsuit> a" in sum_ideals_la1 [of "R" "mx"], assumption+)
 apply (subgoal_tac "(mx \<^bold>+\<^sub>R R \<diamondsuit> a) \<in> {J. ideal R J \<and> mx \<subseteq> J}")
 prefer 2 apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}") 
 apply simp apply simp apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> a \<noteq>  mx") apply simp
 apply (rule contrapos_pp, simp+)
 apply (frule_tac ?I2.0 = "R \<diamondsuit> a" in sum_ideals_la2 [of "R" "mx"], assumption+) apply (frule_tac a = a in a_in_principal [of "R"], assumption+)
 apply (frule_tac A = "R \<diamondsuit> a" and B = "mx \<^bold>+\<^sub>R R \<diamondsuit> a" and c = a in subsetD, assumption+) apply simp
 apply (simp add:ar_coset_def)

apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "x = mx") apply blast  apply simp
apply (rule r_cosUnit1_1) apply (rule b_ag_group) apply (simp add:ring_def)
apply (subgoal_tac "ideal R mx") apply (simp add:ideal_def asubgroup_def)
apply (simp add:maximal_ideal_def)

apply assumption
done

constdefs
 ring_field_condition::"('a, 'm) RingType_scheme \<Rightarrow> bool"
 "ring_field_condition R  == \<forall>x\<in>(carrier R - {0\<^sub>R}). \<exists>y\<in>carrier R. 
                                               x \<cdot>\<^sub>R y = 1\<^sub>R" 
constdefs
 ring_iOp :: "('a, 'm) RingType_scheme \<Rightarrow> 'a  \<Rightarrow> 'a "
 "ring_iOp R == \<lambda>x. (SOME y. y \<in> carrier R \<and> x \<cdot>\<^sub>R y = 1\<^sub>R)"

constdefs
 ringF ::  "('a, 'm) RingType_scheme \<Rightarrow> \<lparr> carrier :: 'a set,
 pOp :: ['a, 'a] \<Rightarrow> 'a, mOp ::'a \<Rightarrow> 'a, zero :: 'a, tOp :: ['a, 'a] \<Rightarrow> 'a,
  one ::'a, iOp ::'a \<Rightarrow> 'a\<rparr>" 

"ringF R  == \<lparr> carrier = carrier R, pOp = pOp R, mOp = mOp R, zero = zero R, 
 tOp = tOp R, one = one R, iOp = ring_iOp R\<rparr>"

lemma ring_iOp:"\<lbrakk>ring R; ring_field_condition R; x \<in> carrier R - {0\<^sub>R}\<rbrakk> \<Longrightarrow> 
                     ring_iOp R x \<in> carrier R \<and> ring_iOp R x \<noteq> 0\<^sub>R"
apply (simp add:ring_iOp_def)
apply (rule someI2_ex) 
apply (simp add:ring_field_condition_def) apply blast
apply (simp add:ring_field_condition_def)
 apply (thin_tac "\<forall>x\<in>carrier R - {0\<^sub>R}.
               \<exists>y\<in>carrier R. RingType.tOp R x y = RingType.one R")
 apply (erule conjE)+
 apply (rule contrapos_pp, simp+) apply (frule sym) 
 apply (thin_tac "RingType.tOp R x (0\<^sub>R) = RingType.one R")
 apply (simp add:ring_times_x_0)
 apply (frule ring_l_one[of "R" "x"], assumption+) apply simp
 apply (simp add:ring_times_0_x)
done

lemma ringF_field:"\<lbrakk>ring R; ring_field_condition R\<rbrakk> \<Longrightarrow>
                                             field (ringF R)"
apply (simp add:field_def)
apply (rule conjI)
 prefer 2
 apply (rule conjI)
 apply (rule univar_func_test) apply (rule ballI)
 apply simp  apply (erule conjE) apply (simp add:ringF_def)
 apply (rule ring_iOp, assumption+) apply simp
apply (rule ballI)
 apply (simp add:ringF_def)
 apply (frule_tac x = x in ring_iOp[of "R"], assumption+)
 apply simp
 apply (erule conjE)+
 apply (subst ring_iOp_def)
 apply (simp add:ring_field_condition_def)
 apply (subgoal_tac "\<exists>y\<in>carrier R. RingType.tOp R x y = RingType.one R")
 prefer 2 apply blast
 apply (thin_tac "\<forall>x\<in>carrier R - {0\<^sub>R}.
              \<exists>y\<in>carrier R. RingType.tOp R x y = RingType.one R")
 apply (rule someI2_ex) apply blast 
 apply (simp add:ring_tOp_commute)
apply (simp add:ring_def[of "ringF R"]) 
 apply (rule conjI)
 prefer 2
 apply (simp add:ring_def ringF_def)
 apply (rule impI) apply (rule ballI) apply (fold ring_def)
 apply (simp add:ring_r_one)
apply (simp add:agroup_def[of "ringF R"]) 
 apply (frule ring_is_ag[of "R"])
 apply (simp add:ringF_def)
 apply (simp add:agroup_def) apply (fold agroup_def)
 apply (rule impI) apply (rule ballI)
 apply (simp add:ag_r_zero)
done

lemma residue_field_condition:"\<lbrakk> ring R; maximal_ideal R mx\<rbrakk> \<Longrightarrow>
       ring_field_condition (qring R mx)"
apply (simp add:ring_field_condition_def) apply (rule ballI)
apply simp apply (erule conjE)
 apply (simp add:residue_fieldTr[of "R" "mx"])
done

lemma qringF_field:"\<lbrakk>ring R; maximal_ideal R mx\<rbrakk> \<Longrightarrow> 
                                 field (ringF (qring R mx))"
apply (frule maximal_ideal_ideal[of "R" "mx"], assumption+)
apply (frule qring_ring [of "R" "mx"], assumption+)
 apply (frule residue_field_condition[of "R" "mx"], assumption+)
 apply (simp add:ringF_field)
done

lemma mulDisj:"\<lbrakk> ring R; mul_closed_set R S; 1\<^sub>R \<in> S; 0\<^sub>R \<notin> S; 
T = {I. ideal R I \<and> S \<inter> I = {}}; maximal_set T mx \<rbrakk> \<Longrightarrow> prime_ideal R mx"
apply (simp add:prime_ideal_def)
apply (rule conjI) apply (simp add:maximal_set_def)
apply (rule conjI) apply (simp add:maximal_set_def)
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac " S \<inter> mx = {}")
apply auto

apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "\<forall>z\<in>carrier R. z \<notin> mx \<longrightarrow> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> z) \<noteq> {}")
 apply (subgoal_tac "S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> x) \<noteq> {}") 
 apply (subgoal_tac "S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> y) \<noteq> {}")
 apply (thin_tac "\<forall>z\<in>carrier R. z \<notin> mx \<longrightarrow> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> z) \<noteq> {}")
apply (frule_tac  A = S and B = "mx \<^bold>+\<^sub>R R \<diamondsuit> x" in nonempty_int) 
apply (frule_tac  A = S and B = "mx \<^bold>+\<^sub>R R \<diamondsuit> y" in nonempty_int) 
apply (subgoal_tac "\<forall>xa. \<forall>ya. xa \<in> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> x) \<and> ya \<in> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> y) \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>xa. xa \<in> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> x)")
 apply (thin_tac "\<exists>x. x \<in> S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> y)")
apply (rule allI)+ apply (rule impI)
 apply (thin_tac "S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> x) \<noteq> {}")
 apply (thin_tac "S \<inter> (mx \<^bold>+\<^sub>R R \<diamondsuit> y) \<noteq> {}")
 apply (thin_tac "y \<notin> mx") apply (thin_tac "x \<notin> mx")

prefer 2 apply simp
prefer 2 apply simp
prefer 2 apply (rule ballI) apply (rule impI)
apply (subgoal_tac "mx \<subset> mx \<^bold>+\<^sub>R (R \<diamondsuit> z)") prefer 2
apply (rule id_ideal_psub_sum [of "R" "mx" _], assumption+) 
 apply (simp add:maximal_set_def) apply assumption+
 apply (frule_tac  ?I2.0 = "R \<diamondsuit> z" in sum_ideals [of "R" "mx"])
 apply (simp add:maximal_set_def) apply (simp add:principal_ideal)
 apply (simp add:maximal_set_def)
 apply (rule contrapos_pp, simp+)
 apply (frule psubset_imp_subset)
 apply (subgoal_tac "mx = mx \<^bold>+\<^sub>R R \<diamondsuit> z") 
 apply (subgoal_tac "z \<in> mx")
 apply simp
 apply (subgoal_tac "R \<diamondsuit> z \<subseteq> mx \<^bold>+\<^sub>R R \<diamondsuit> z") prefer 2
apply (rule sum_ideals_la2, assumption+) apply (simp add:CollectI)
 apply (simp add:principal_ideal)
 apply (frule a_in_principal, assumption+)
 apply (subgoal_tac "z \<in> mx \<^bold>+\<^sub>R R \<diamondsuit> z") 
 apply blast apply (simp add:subsetD)
apply blast

apply (erule conjE)
apply (simp add:asettOp_def settOp_def) 
 apply (erule conjE)+
 apply (frule ring_is_ag)
 apply (frule agop_gop) apply simp
apply (thin_tac "GroupType.tOp (b_ag R) = pOp R")
apply auto
 apply (simp add:Rxa_def)
 apply (subgoal_tac "\<forall>r1\<in>carrier R. \<forall>r2\<in>carrier R. yb =  r1 \<cdot>\<^sub>R x \<and> yc =  r2 \<cdot>\<^sub>R y \<longrightarrow> False")  apply blast
 apply (thin_tac "\<exists>r\<in>carrier R. yb =  r \<cdot>\<^sub>R x")
 apply (thin_tac "\<exists>r\<in>carrier R. yc =  r \<cdot>\<^sub>R y")
apply (rule ballI)+ apply (rule impI) apply (erule conjE)
 apply (subgoal_tac "ideal R mx")
 apply (subgoal_tac "(xb +\<^sub>R yb) \<cdot>\<^sub>R (xc +\<^sub>R yc) \<in> S")
 apply (frule_tac a = xb and b = yb and x = xc and y = yc in ring_distrib3)
 apply (rule ideal_subset, assumption+)
 apply (simp add:ring_tOp_closed)
 apply (rule ideal_subset, assumption+)
 apply (simp add:ring_tOp_closed)
 apply simp
apply (thin_tac "( xb +\<^sub>R  r1 \<cdot>\<^sub>R x) \<cdot>\<^sub>R ( xc +\<^sub>R  r2 \<cdot>\<^sub>R y) =
  xb \<cdot>\<^sub>R xc +\<^sub>R  xb \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y) +\<^sub>R   r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R xc +\<^sub>R r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y)")
 apply (subgoal_tac " xb \<cdot>\<^sub>R xc +\<^sub>R  xb \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y) +\<^sub>R   r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R xc +\<^sub>R
               r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y) \<in> mx")
 apply (subgoal_tac "S \<inter> mx \<noteq> {}")
 apply (simp add:maximal_set_def)
 apply blast
 apply (thin_tac " xb \<cdot>\<^sub>R xc +\<^sub>R  xb \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y) +\<^sub>R   r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R xc +\<^sub>R
               r1 \<cdot>\<^sub>R x \<cdot>\<^sub>R ( r2 \<cdot>\<^sub>R y) \<in> S")
apply (rule ideal_pOp_closed, assumption+)+
 apply (rule ideal_ring_multiple1, assumption+)
 apply (simp add:ideal_subset)
 apply (rule ideal_ring_multiple1, assumption+)
 apply (simp add:ring_tOp_closed)
 apply (rule ideal_ring_multiple, assumption+)
 apply (simp add:ring_tOp_closed)
 apply (subst ring_tOp_rel, assumption+)
 apply (rule ideal_ring_multiple, assumption+)
  apply (simp add:ring_tOp_closed)
apply (simp add:mul_closed_set_def)
apply (simp add:maximal_set_def)
done

lemma ex_mulDisj_maximal:"\<lbrakk> ring R; mul_closed_set R S; 0\<^sub>R \<notin> S; 1\<^sub>R \<in> S;  
T = {I. ideal R I \<and> S \<inter> I = {}}\<rbrakk> \<Longrightarrow>  \<exists>mx. maximal_set T mx" 
apply (cut_tac S="{ I. ideal R I \<and> S \<inter> I = {}}" in Zorn_Lemma2)
prefer 2
  apply (simp add:maximal_set_def)

apply (rule ballI)
apply (case_tac "c = {}")
 apply (frule zero_ideal) apply blast

apply (subgoal_tac "c \<in> chain {I. ideal R I \<and> I \<subset> carrier R}")
apply (frule chain_un, assumption, assumption+)
 apply (subgoal_tac "S \<inter> (\<Union> c) = {}")
 apply (subgoal_tac "\<forall>x\<in>c. x \<subseteq> \<Union> c") apply blast
apply (rule ballI) apply (rule subsetI) apply (simp add:CollectI)
 apply blast
apply (rule contrapos_pp) apply simp+
 apply (frule_tac A = S and B = "\<Union> c" in nonempty_int)
 apply (subgoal_tac "\<forall>s. s \<in> S \<inter> \<Union>c \<longrightarrow> False")
 apply blast apply (thin_tac "\<exists>s. s \<in> S \<inter> \<Union>c")
 apply (thin_tac "S \<inter> \<Union>c \<noteq> {}")
 apply (rule allI) apply (rule impI)
 apply (simp add:Inter_def) 
 apply (subgoal_tac "\<forall>X\<in>c. s \<in> S \<and> s \<in> X \<longrightarrow> False") 
 apply blast apply (thin_tac "s \<in> S \<and> (\<exists>X\<in>c. s \<in> X)")
 apply (rule ballI) apply (rule impI) apply (erule conjE)
 apply (simp add:chain_def) apply (erule conjE)
  apply (subgoal_tac "X \<in> {I. ideal R I \<and> S \<inter> I = {}}")
  apply (simp add:CollectI)
  apply blast
  apply (rule subsetD, assumption+)

apply (simp add:chain_def)
 apply (rule subsetI)
 apply (rename_tac c Z)
 apply (erule conjE)
 apply (frule_tac A = c and B = "{I. ideal R I \<and> S \<inter> I = {}}" and c = Z in 
              subsetD, assumption+)
 apply (simp add:CollectI)
apply (rule contrapos_pp, simp+) apply (simp add:psubset_def)
 apply (erule conjE) apply (subgoal_tac "Z \<subseteq> carrier R") apply simp
 apply (subgoal_tac "S \<subseteq> carrier R")
 apply (simp add:Int_absorb2 [of "S" "carrier R"])
 apply (rule subsetI) apply (simp add:mul_closed_set_def)
 apply (frule conj_1) apply (rule subsetD, assumption+)
apply (rule subsetI)
 apply (rule ideal_subset, assumption+)
done

lemma ex_mulDisj_prime:"\<lbrakk> ring R; mul_closed_set R S; 0\<^sub>R \<notin> S; 1\<^sub>R \<in> S \<rbrakk> \<Longrightarrow> 
                            \<exists>mx. prime_ideal R mx \<and> S \<inter> mx = {}" 
apply (subgoal_tac "\<exists>mx. maximal_set {I. ideal R I \<and> S \<inter> I = {}} mx")
apply (subgoal_tac "\<forall>mx.(maximal_set {I. ideal R I \<and> S \<inter> I = {}} mx) \<longrightarrow> 
                              (prime_ideal R mx) \<and> S \<inter> mx = {}")
apply blast
apply (rule allI) apply (rule impI)
 apply (simp add:mulDisj [of "R" "S" "{I. ideal R I \<and> S \<inter> I = {}}"])
 apply (simp add:maximal_set_def CollectI)
apply (simp add:ex_mulDisj_maximal)
done

lemma nilradTr1:"\<lbrakk>ring R; \<not> zeroring R\<rbrakk> \<Longrightarrow> nilrad R = \<Inter> {p. prime_ideal R p}"
apply (rule equalityI)
 (* nilrad R \<subseteq> \<Inter>Collect (prime_ideal R) *)
apply (rule subsetI)
 apply (simp add:nilrad_def CollectI nilpotent_def) 
 apply (erule conjE)
 apply (rule allI) apply (rule impI)
 apply (subgoal_tac "0\<^sub>R \<in> xa")
 apply (rule npow_in_prime, assumption+)
 apply (simp add:NSet_def)
 apply (subgoal_tac "\<forall>n.  x^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R \<longrightarrow> x^\<^sup>R\<^sup> \<^sup>n \<in> xa")
 apply blast apply (thin_tac "\<exists>n. x^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R")
 apply (rule allI) apply (rule impI)
 apply simp
 apply (rule ideal_zero, assumption+) apply (simp add:prime_ideal_def)
apply (rule subsetI) apply (subgoal_tac "x \<in> carrier R")
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "0\<^sub>R \<notin> {s. \<exists>n. s = npow R x n} \<and> 
                                  1\<^sub>R \<in> {s. \<exists>n. s = npow R x n}")
apply (erule conjE)
 apply (subgoal_tac "\<exists>mx. prime_ideal R mx \<and> {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n} \<inter> mx = {}")
 apply (subgoal_tac "\<exists>mx. prime_ideal R mx \<and> x \<notin> mx")
apply blast
apply (subgoal_tac "\<forall>mx. prime_ideal R mx \<and> {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n} \<inter> mx = {}
         \<longrightarrow> prime_ideal R mx \<and> x \<notin> mx")
apply blast
 apply (thin_tac "\<exists>mx. prime_ideal R mx \<and> {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n} \<inter> mx = {}") 
apply (rule allI) apply (rule impI)
apply (rule conjI) apply simp apply (erule conjE)
apply (subgoal_tac "x \<in> {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n}") apply blast
apply (subgoal_tac "x = x^\<^sup>R\<^sup> \<^sup>1") apply blast
apply simp apply (simp add:ring_r_one[THEN sym])
apply (rule ex_mulDisj_prime, assumption+)
  (* mul_closed_set {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n} step1 *)
apply (simp add:mul_closed_set_def)
 apply (rule conjI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply (subgoal_tac "\<forall>n. xa = x^\<^sup>R\<^sup> \<^sup>n \<longrightarrow> xa \<in> carrier R")
 apply blast apply (rule allI) apply (rule impI)
 apply (simp add:npClose)
   (* mul_closed_set {s. \<exists>n. s = x^\<^sup>R\<^sup> \<^sup>n} step2 *)
 apply (rule allI) apply (rule impI)
 apply (rule allI) apply (rule impI)
apply (subgoal_tac "\<forall>n. \<forall>m. s =  x^\<^sup>R\<^sup> \<^sup>n \<and> t = x^\<^sup>R\<^sup> \<^sup>m \<longrightarrow> s \<cdot>\<^sub>R t = x^\<^sup>R\<^sup> \<^sup>(n + m)")
 apply blast
apply (rule allI) apply (rule allI) apply (rule impI)
apply (frule conj_1) apply (frule conj_2) apply (simp add:npMulDistr)
 apply assumption+
apply (rule conjI)
 apply (thin_tac "\<forall>xa. prime_ideal R xa \<longrightarrow> x \<in> xa")
 apply (simp add:nilrad_def nilpotent_def)
 apply (rule allI) apply (rule not_sym) apply (simp add:NSet_def)
 apply (subgoal_tac "1\<^sub>R = x^\<^sup>R\<^sup> \<^sup>0") apply blast apply simp
apply (simp add:Int_def) 
apply (frule ex_mulDisj_prime [of "R" "{1\<^sub>R}"])
 apply (simp add:mul_closed_set_def) 
 apply (rule conjI) apply (simp add:ring_def)
 apply (rule ring_r_one, assumption) apply (simp add:ring_def)
 apply simp
 apply (simp add:Zero_ring1 [THEN not_sym])
 apply simp
apply (subgoal_tac "\<forall>mm. prime_ideal R mm \<longrightarrow> x \<in> mm \<longrightarrow> x \<in> carrier R") 
 apply blast apply (thin_tac "\<exists>mx. prime_ideal R mx \<and> {1\<^sub>R} \<inter> mx = {}")
apply (rule allI) apply (rule impI) apply (rule impI)
 apply (subgoal_tac "ideal R mm")
 apply (rule ideal_subset, assumption+) apply (simp add:prime_ideal_def)
done

lemma nonilp_residue_nilrad:"\<lbrakk> ring R; \<not> zeroring R; x \<in> carrier R; 
  nilpotent (qring R (nilrad R)) (x \<uplus>\<^sub>R (nilrad R))\<rbrakk> \<Longrightarrow>
                   x \<uplus>\<^sub>R (nilrad R) = 0\<^sub>(qring R (nilrad R))"
apply (simp add:nilpotent_def)
apply (subgoal_tac "\<forall>n\<in>NSet. (x \<uplus>\<^sub>R (nilrad R))^\<^sup>(qring R (nilrad R))\<^sup> \<^sup>n 
 = 0\<^sub>(qring R (nilrad R)) \<longrightarrow> x \<uplus>\<^sub>R (nilrad R) = 0\<^sub>(qring R (nilrad R))")
apply blast
apply (thin_tac "\<exists>n\<in>NSet. (x \<uplus>\<^sub>R (nilrad R))^\<^sup>(qring R (nilrad R))\<^sup> \<^sup>n = 0\<^sub>(qring R (nilrad R))")
apply (rule ballI) apply (rule impI)
apply (subgoal_tac "(x \<uplus>\<^sub>R (nilrad R))^\<^sup>(qring R (nilrad R))\<^sup> \<^sup>n =
          (npow R x n) \<uplus>\<^sub>R (nilrad R)") apply simp
apply (subgoal_tac " 0\<^sub>(qring R (nilrad R)) = nilrad R") apply simp
apply (subgoal_tac "(npow R x n) \<in> x^\<^sup>R\<^sup> \<^sup>n \<uplus>\<^sub>R (nilrad R) ") apply simp
apply (subgoal_tac "x \<in> nilrad R")
apply (simp add:ar_coset_def)
apply (rule r_cosUnit1_1 [of "b_ag R" "nilrad R" "x"])
 apply (rule b_ag_group) apply (simp add:ring_def)
 apply (frule id_nilrad_ideal)
apply (simp add:ideal_def asubgroup_def) apply assumption
apply (simp add:nilrad_def nilpotent_def)
apply (subgoal_tac "\<exists>na\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>na = 0\<^sub>R")
 (* thm npMulExp *)
apply (subgoal_tac "\<forall>na\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>na = 0\<^sub>R \<longrightarrow> 
                                (\<exists>n\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n = 0\<^sub>R)")
apply blast apply (thin_tac "\<exists>na\<in>NSet. x^\<^sup>R\<^sup> \<^sup>n^\<^sup>R\<^sup> \<^sup>na = 0\<^sub>R")
apply (rule ballI) apply (rule impI)
apply (simp add:npMulExp) apply (simp add:NSet_def) apply blast
apply simp

prefer 3 apply (rule npQring [of "R" "nilrad R" "x"], assumption+)  
 apply (simp add:id_nilrad_ideal) apply assumption
 apply (thin_tac "(x \<uplus>\<^sub>R (nilrad R))^\<^sup>(qring R (nilrad R))\<^sup> \<^sup>n = nilrad R")
 apply (unfold ar_coset_def)
 apply (rule  aInR_cos) apply (rule b_ag_group) apply (simp add:ring_def)
apply (subgoal_tac "ideal R (nilrad R)")
 apply (simp add:ideal_def asubgroup_def) apply (simp add:id_nilrad_ideal)
 apply (simp add:b_ag_def npClose)
 apply (simp add:qring_def agroup_def)
done

lemma ex_contid_maximal:"\<lbrakk> ring R; S = {1\<^sub>R}; 0\<^sub>R \<notin> S; ideal R I; I \<inter> S = {};
T = {J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}\<rbrakk> \<Longrightarrow> \<exists>mx. maximal_set T mx" 
apply (cut_tac S="{J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}" in Zorn_Lemma2)
apply (rule ballI)
apply (case_tac "c = {}") (** case c = {} **)
 apply blast             (** case c = {} done **)
     (** existence of sup in c **)
apply (subgoal_tac "\<Union>c\<in>{J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J} \<and> 
                                         (\<forall>x\<in>c. x \<subseteq>  \<Union>c)")  
 apply blast
apply (rule conjI)
apply (simp add:CollectI)
apply (subgoal_tac "c \<in> chain {I. ideal R I \<and> I \<subset> carrier R}")
apply (rule conjI)
apply (simp add:chain_un)
apply (rule conjI)
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "\<forall>K\<in>c. (1\<^sub>R)\<in>K \<longrightarrow> False") apply blast
 apply (thin_tac "Bex c (op \<in> (1\<^sub>R))")
 apply (rule ballI) apply (rule impI)
 apply (thin_tac " c \<in> chain {I. ideal R I \<and> I \<subset> carrier R}")
 apply (simp add:chain_def)
 apply (frule conj_1)
 apply (subgoal_tac "K \<in> {J. ideal R J \<and> 1\<^sub>R \<notin> J \<and> I \<subseteq> J}")
 apply (simp add:CollectI)
 apply (rule subsetD, assumption+)
 apply (thin_tac "c \<in> chain {I. ideal R I \<and> I \<subset> carrier R}")
 apply (simp add:chain_def)
 apply (frule conj_1)
 apply (subgoal_tac "\<forall>X\<in>c. I \<subseteq> X")
 apply blast
 apply (rule ballI)
 apply (subgoal_tac "X \<in> {J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J}")
 apply (simp add:CollectI)
 apply (rule subsetD) apply simp apply assumption

apply (simp add:chain_def)
 apply (rule subsetI) 
 apply (frule conj_1)
 apply (subgoal_tac "x \<in> {J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J}")
 apply (simp add:CollectI) 
 apply (subgoal_tac "(1\<^sub>R) \<notin> x")
 apply (rule contrapos_pp) apply simp+
 apply (simp add:psubset_def)
 apply (simp add:ideal_subset1)
 apply (simp add:ring_def)
 apply blast
 apply (rule subsetD) apply simp apply assumption
apply blast     (** exists sup in c done **)
 (* existence of maximal set *)
apply (unfold maximal_set_def) apply simp
done

lemma contid_maximal:"\<lbrakk> ring R; S = {1\<^sub>R}; 0\<^sub>R \<notin> S; ideal R I; I \<inter> S = {};
T = {J. ideal R J \<and> S \<inter> J = {} \<and> I \<subseteq> J}; maximal_set T mx\<rbrakk> \<Longrightarrow> 
                                                maximal_ideal R mx"

apply (simp add:maximal_set_def maximal_ideal_def)
apply (erule conjE)+
apply (rule equalityI)
  (** {J. ideal R J \<and> mx \<subseteq> J} \<subseteq> {mx, carrier R} **) 
  apply (rule subsetI) apply (simp add:CollectI)
apply (erule conjE)
 apply (case_tac "x = mx") apply simp apply simp
 apply (subgoal_tac "1\<^sub>R \<in> x")
 apply (rule_tac  I = x in ideal_inc_one [of "R"], assumption+)
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "mx = x") apply (rotate_tac -3)
 apply (frule not_sym) apply simp apply blast
apply (rule subsetI) apply (simp add:CollectI)
 apply (case_tac "x = mx") apply simp apply simp
 apply (simp add:whole_ideal)
 apply (rule subsetI) apply (rule ideal_subset [of "R" "mx"], assumption+)
done

lemma ideal_contained_maxid:"\<lbrakk> ring R; \<not>(zeroring R); ideal R I; (1\<^sub>R) \<notin> I \<rbrakk>
 \<Longrightarrow>  \<exists>mx. maximal_ideal R mx \<and> I \<subseteq> mx"
apply (subgoal_tac "\<exists>mx. maximal_set {J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J} mx")
apply (subgoal_tac "\<forall>mx. maximal_set {J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J} mx
 \<longrightarrow> maximal_ideal R mx \<and> I \<subseteq> mx") 
apply blast
 apply (thin_tac "\<exists>mx. maximal_set {J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J} mx")
apply (rule allI) apply (rule impI)
apply (rule conjI)
apply (rule  contid_maximal [of "R" "{1\<^sub>R}" "I" 
              "{J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J}" _], assumption+)
apply simp
apply simp 
apply (simp add:Zero_ring1 [THEN not_sym]) 
apply assumption+
apply (simp add:Int_def) apply blast
apply simp
apply assumption
apply (simp add:maximal_set_def)

apply (rule  ex_contid_maximal [of "R" "{1\<^sub>R}" "I"
             "{J. ideal R J \<and> {1\<^sub>R} \<inter> J = {} \<and> I \<subseteq> J}"], assumption+)
apply simp+
apply (rule Zero_ring1 [THEN not_sym], assumption+)
apply (simp add:Int_def) apply blast
apply simp
done

lemma nonunit_principal_id:"\<lbrakk> ring R; a \<in> carrier R; \<not> (unit R a) \<rbrakk> \<Longrightarrow>
      (R \<diamondsuit> a) \<noteq> (carrier R)"
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "(1\<^sub>R) \<in> R \<diamondsuit> a") apply (thin_tac "R \<diamondsuit> a = carrier R")
apply (simp add:Rxa_def)
apply (simp add:unit_def)
apply (simp add:ring_tOp_commute) 
apply (subgoal_tac "\<forall>y\<in>carrier R.  1\<^sub>R \<noteq> y \<cdot>\<^sub>R a")
apply blast apply (thin_tac "\<exists>r\<in>carrier R. 1\<^sub>R =  r \<cdot>\<^sub>R a")
apply (rule ballI)
apply (subgoal_tac "y \<cdot>\<^sub>R a \<noteq> 1\<^sub>R") apply (rule not_sym, assumption+)
apply simp
apply (subgoal_tac "(1\<^sub>R) \<in> carrier R")
apply simp
apply (simp add:ring_def)
done

lemma nonunit_contained_maxid:"\<lbrakk> ring R; \<not>(zeroring R); a \<in> carrier R; 
 \<not> unit R a \<rbrakk>  \<Longrightarrow>  \<exists>mx. maximal_ideal R mx \<and> a \<in>  mx"
apply (insert ideal_contained_maxid [of "R" "R \<diamondsuit> a"])
apply simp+
apply (simp add:principal_ideal)
apply (subgoal_tac "1\<^sub>R \<notin> R \<diamondsuit> a") apply simp
apply (subgoal_tac "\<forall>mx. maximal_ideal R mx \<and> R \<diamondsuit> a \<subseteq> mx \<longrightarrow> a \<in> mx")
apply blast apply (thin_tac "\<exists>mx. maximal_ideal R mx \<and> R \<diamondsuit> a \<subseteq> mx")
apply (rule allI) apply (rule impI)
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "maximal_ideal R mx \<and> R \<diamondsuit> a \<subseteq> mx")
 apply (frule a_in_principal, assumption+)
 apply (rule subsetD, assumption+)

apply (frule nonunit_principal_id, assumption+)
apply (rule contrapos_pp) apply simp+
apply (frule ideal_inc_one) 
apply (frule principal_ideal, assumption+) 
apply simp
done

constdefs
 local_ring :: "('a, 'more) RingType_scheme \<Rightarrow> bool"
 "local_ring R == ring R \<and> \<not> zeroring R \<and> card {mx. maximal_ideal R mx} = 1"

lemma local_ring_diff:"\<lbrakk>ring R; \<not> zeroring R;  ideal R mx; mx \<noteq> carrier R;
  \<forall>a\<in> (carrier R - mx). unit R a \<rbrakk> \<Longrightarrow> local_ring R \<and> maximal_ideal R mx" 

apply (subgoal_tac "\<forall>m1. maximal_ideal R m1 \<longrightarrow> m1 = mx")
apply (simp add:local_ring_def) 
apply (subgoal_tac "Collect (maximal_ideal R) = {mx}")
apply simp   
apply (frule id_maximal_Exist, assumption+)
apply blast

apply (rule equalityI)
  apply (rule subsetI) apply (simp add:CollectI) 
  apply (rule subsetI) apply (simp add:CollectI)
  apply (thin_tac "x = mx")
  apply (frule id_maximal_Exist, assumption+)
  apply blast

apply (rule allI) apply (rule impI)
apply (subgoal_tac "m1 \<subseteq> mx")
 apply (simp add:maximal_ideal_def)
 apply (subgoal_tac "{J. ideal R J \<and> m1 \<subseteq> J} = {m1, carrier R}")
 apply (subgoal_tac "mx \<in> {J. ideal R J \<and> m1 \<subseteq> J}")
 apply (simp add:CollectI)
  apply (thin_tac "{J. ideal R J \<and> m1 \<subseteq> J} = {m1, carrier R}")
 apply blast
 apply simp
 
 (** prove  m1 \<subseteq> mx **)
apply (rule contrapos_pp) apply simp+
apply (simp add:subset_def)
apply (subgoal_tac "\<forall>x\<in>m1. x\<notin> mx \<longrightarrow> False")
apply blast apply (thin_tac " \<exists>x\<in>m1. x \<notin> mx")
apply (rule ballI) apply (rule impI)
apply (subgoal_tac "unit R x")
apply (subgoal_tac "1\<^sub>R \<in> m1") apply (simp add:maximal_ideal_def)
apply (subgoal_tac "m1 = carrier R") apply simp
apply (simp add:ring_def)
apply (subgoal_tac "x \<in> carrier R")
apply (rule ideal_inc_unit1, assumption+)
apply (simp add:maximal_ideal_def) apply assumption
 apply (thin_tac "ideal R mx")
apply (rule ideal_subset, assumption+)
 apply (subgoal_tac "ideal R m1")
 apply simp
 apply (simp add:maximal_ideal_def)
 apply assumption
 apply (subgoal_tac "x \<in> carrier R - mx")
 apply blast
apply (subgoal_tac "x \<in> carrier R") apply blast

apply (subgoal_tac "ideal R m1")
 apply (thin_tac "ideal R mx")
 apply (rule ideal_subset, assumption+)
 apply (simp add:maximal_ideal_def)
done

lemma localring_unit:"\<lbrakk> ring R; \<not> zeroring R; maximal_ideal R mx; 
\<forall>x. x\<in>mx \<longrightarrow> unit R (x +\<^sub>R (1\<^sub>R)) \<rbrakk> \<Longrightarrow> local_ring R"
apply (simp add:local_ring_def)
apply (subgoal_tac "Collect (maximal_ideal R) = {mx}")
apply simp
apply (subgoal_tac "\<forall>mm. maximal_ideal R mm \<longrightarrow> mm = mx") 
apply blast
apply (rule allI) apply (rule impI)
apply (rule contrapos_pp) apply simp+
apply (subgoal_tac "\<exists>x\<in>mm. x \<notin> mx")
apply (subgoal_tac "\<forall>x\<in>mm. x\<notin> mx \<longrightarrow> False")
apply blast apply (thin_tac "\<exists>x\<in>mm. x \<notin> mx")
apply (rule ballI) apply (rule impI)
apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x = carrier R")
apply (simp add:asettOp_def settOp_def)
apply (subgoal_tac "1\<^sub>R \<in>  {z. \<exists>xa\<in>mx. \<exists>y\<in>R \<diamondsuit> x.  GroupType.tOp (b_ag R) xa y = z}")
 apply (thin_tac "{z. \<exists>xa\<in>mx. \<exists>y\<in>R \<diamondsuit> x.  GroupType.tOp (b_ag R) xa y = z} = carrier R")
 apply (simp add:CollectI)
 apply (subgoal_tac "GroupType.tOp (b_ag R) = pOp R") apply simp
 apply (subgoal_tac "\<forall>xa\<in>mx. \<forall>y\<in>R \<diamondsuit> x.  xa +\<^sub>R y = 1\<^sub>R \<longrightarrow> False") apply blast
 apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (subgoal_tac "y = (-\<^sub>R xa) +\<^sub>R (1\<^sub>R)")
apply (subgoal_tac "-\<^sub>R xa \<in> mx")   
apply (subgoal_tac "unit R y")
apply (subgoal_tac "y \<in> mm")
  apply (thin_tac "y =  -\<^sub>R xa +\<^sub>R 1\<^sub>R")
apply (subgoal_tac "ideal R mm") prefer 2 apply (simp add:maximal_ideal_def)
 apply (thin_tac "x \<in> mm") apply (thin_tac "xa \<in> mx") 
 apply (thin_tac " -\<^sub>R xa \<in> mx")
 apply (frule ideal_subset, assumption+)
apply (frule ideal_inc_unit1, assumption+)
apply (subgoal_tac "1\<^sub>R \<in> mm") apply (thin_tac "mm = carrier R")
apply (simp add:maximal_ideal_def)

apply (simp add:ring_def)
 apply (thin_tac " y =  -\<^sub>R xa +\<^sub>R 1\<^sub>R")
 apply (thin_tac "\<exists>xa\<in>mx. \<exists>y\<in>R \<diamondsuit> x.  xa +\<^sub>R y = 1\<^sub>R")
apply (simp add:Rxa_def)
apply (subgoal_tac "\<forall>r\<in>carrier R. y = r \<cdot>\<^sub>R x \<longrightarrow> y \<in> mm")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. y =  r \<cdot>\<^sub>R x")
 apply (rule ballI) apply (rule impI) apply simp
 apply (rule ideal_ring_multiple, assumption+) 
 apply (simp add:maximal_ideal_def) apply assumption+ 
apply simp apply (rule ideal_inv1_closed, assumption+)
 apply (simp add:maximal_ideal_def) apply assumption+
 apply (rule ag_eq_sol1) apply (simp add:ring_def)
  apply (subgoal_tac "ideal R mx")
  apply (rule ideal_subset, assumption+)
 apply (simp add:maximal_ideal_def)
apply (simp add:Rxa_def) 
 apply (subgoal_tac "\<forall>r\<in>carrier R. y =  r \<cdot>\<^sub>R x \<longrightarrow> y \<in> carrier R")
 apply blast apply (thin_tac "\<exists>r\<in>carrier R. y =  r \<cdot>\<^sub>R x")
 apply (rule ballI) apply (rule impI) apply simp
 apply (rule ring_tOp_closed)
  apply assumption+
  apply (subgoal_tac "ideal R mm")
  apply (simp add:ideal_subset) apply (simp add:maximal_ideal_def)
apply (simp add:ring_def)
apply assumption
apply (simp add:b_ag_def)
apply (simp add:ring_def)

apply (subgoal_tac "mx \<subset> mx \<^bold>+\<^sub>R R \<diamondsuit> x")
 apply (thin_tac "\<forall>x. x \<in> mx \<longrightarrow> unit R ( x +\<^sub>R 1\<^sub>R)")
 apply (simp add:maximal_ideal_def [of "R" "mx"])
 apply (simp add:psubset_def)
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "ideal R mx \<and> 1\<^sub>R \<notin> mx \<and> 
                 {J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "mx \<subseteq> mx \<^bold>+\<^sub>R R \<diamondsuit> x \<and> mx \<noteq> mx \<^bold>+\<^sub>R R \<diamondsuit> x")
 apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "1\<^sub>R \<notin> mx \<and> {J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x \<in> {J. ideal R J \<and> mx \<subseteq> J}")
 apply simp apply (subgoal_tac "mx \<^bold>+\<^sub>R R \<diamondsuit> x \<noteq> mx") apply simp
 apply (rule not_sym, assumption)
 apply (thin_tac "{J. ideal R J \<and> mx \<subseteq> J} = {mx, carrier R}")
 apply (simp add:CollectI)
 apply (rule sum_ideals, assumption+)
  apply (rule principal_ideal, assumption+)
  apply (subgoal_tac "ideal R mm") apply (simp add:ideal_subset)
  apply (simp add:maximal_ideal_def)
  apply (rule id_ideal_psub_sum, assumption+)
   apply (simp add:maximal_ideal_def)
   apply (thin_tac "maximal_ideal R mx")
  apply (subgoal_tac "ideal R mm")
  apply (simp add:ideal_subset)
  apply (simp add:maximal_ideal_def) apply assumption+
   apply (thin_tac " \<forall>x. x \<in> mx \<longrightarrow> unit R ( x +\<^sub>R 1\<^sub>R)") 
apply (rule contrapos_pp) apply simp+ 
apply (subgoal_tac "mm = mx") apply simp
  apply (thin_tac "mm \<noteq> mx")
 apply (subgoal_tac "mm \<subseteq>  mx") apply (thin_tac "\<forall>x\<in>mm. x \<in> mx")
 apply (subgoal_tac "ideal R mx")
 apply (subgoal_tac "1\<^sub>R \<notin> mx")
 apply (thin_tac "maximal_ideal R mx")
 apply (simp add:maximal_ideal_def)
 apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "ideal R mm \<and>
            1\<^sub>R \<notin> mm \<and> {J. ideal R J \<and> mm \<subseteq> J} = {mm, carrier R}")
 apply (frule conj_1) apply (frule conj_2)
  apply (thin_tac "1\<^sub>R \<notin> mm \<and> {J. ideal R J \<and> mm \<subseteq> J} = {mm, carrier R}")
 apply (subgoal_tac "mx \<in> {J. ideal R J \<and> mm \<subseteq> J}")
 apply (simp add:CollectI)
 apply (case_tac " mx = carrier R")
 apply (subgoal_tac "1\<^sub>R \<in> mx") apply blast
 apply (simp add:ring_def) 
 apply simp

 apply (thin_tac "{J. ideal R J \<and> mm \<subseteq> J} = {mm, carrier R}")
 apply (simp add:CollectI) apply (simp add:maximal_ideal_def)
 apply (simp add:maximal_ideal_def)
 apply (simp add:subset_def)
done


constdefs
 J_rad ::"('a, 'more) RingType_scheme \<Rightarrow> 'a set"
  "J_rad R == \<Inter> {mx. maximal_ideal R mx}"

lemma J_rad_unit:"\<lbrakk>ring R; \<not> zeroring R; x \<in> J_rad R\<rbrakk> \<Longrightarrow> 
            \<forall>y. (y\<in> carrier R \<longrightarrow> unit R (1\<^sub>R +\<^sub>R (-\<^sub>R x) \<cdot>\<^sub>R y))"
apply (rule allI) apply (rule impI)
apply (rule contrapos_pp) apply simp+ 
apply (subgoal_tac "\<exists>mx. maximal_ideal R mx \<and> (1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y) \<in> mx")
apply (subgoal_tac "\<forall>mx. maximal_ideal R mx \<and> (1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y) \<in> mx
   \<longrightarrow> False") apply blast
 apply (thin_tac "\<exists>mx. maximal_ideal R mx \<and>  1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y \<in> mx")
apply (rule allI) apply (rule impI)
apply (subgoal_tac "x \<in> mx")
apply (frule conj_1) apply (frule conj_2)
 apply (thin_tac "maximal_ideal R mx \<and>  1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y \<in> mx")
apply (subgoal_tac "1\<^sub>R \<in> mx")
 apply (simp add:maximal_ideal_def)
 apply (subgoal_tac "\<exists>m\<in>mx.  1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y = m ")
apply (subgoal_tac "\<forall>m\<in>mx. 1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y = m  \<longrightarrow> 1\<^sub>R \<in> mx")
 apply blast apply (thin_tac " Bex mx (op = ( 1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y))")
 apply (rule ballI) apply (rule impI)
apply (subgoal_tac "1\<^sub>R = m +\<^sub>R (-\<^sub>R (-\<^sub>R x) \<cdot>\<^sub>R y)")
 apply simp
 apply (rule ideal_pOp_closed, assumption+)
 apply (simp add:maximal_ideal_def) apply assumption
 apply (subst ring_inv1_1, assumption+)
 apply (thin_tac "m +\<^sub>R -\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y = m")
 apply (thin_tac "m \<in> mx")
 apply (subgoal_tac "ideal R mx")
 apply (frule ideal_subset) apply assumption
 apply assumption
 apply (rule ag_mOp_closed) 
  apply (simp add:ring_def) apply assumption apply (simp add:maximal_ideal_def)
  apply assumption
  apply (subst ag_inv_inv) apply (simp add:ring_def)
  apply (subgoal_tac "ideal R mx")
   apply (rule ideal_subset, assumption+)
   apply (simp add:maximal_ideal_def)
  apply (subgoal_tac "ideal R mx")
  apply (simp add:ideal_ring_multiple1) apply (simp add:maximal_ideal_def)
 apply (rule ag_eq_sol2) apply (simp add:ring_def)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule ag_mOp_closed) apply (simp add:ring_def)
 apply (subgoal_tac "ideal R mx")
 apply (rule ideal_subset, assumption+) apply (simp add:maximal_ideal_def)
  apply assumption+ apply (simp add:ring_def)
 apply (subgoal_tac "ideal R mx") apply (rule ideal_subset, assumption+)
  apply (simp add:maximal_ideal_def) apply assumption
 apply (simp add:elem_some)
 apply (frule conj_1)
 apply (thin_tac "maximal_ideal R mx \<and>  1\<^sub>R +\<^sub>R  (-\<^sub>R x) \<cdot>\<^sub>R y \<in> mx")
 apply (simp add:J_rad_def)
apply (rule nonunit_contained_maxid, assumption+)
apply (rule ag_pOp_closed)
 apply (simp add:ring_def) apply (simp add:ring_def)
 apply (subgoal_tac "x \<in> carrier R")
 apply (rule ring_tOp_closed, assumption)
  apply (rule ag_mOp_closed) apply (simp add:ring_def) apply assumption+
 apply (subgoal_tac "\<exists>m1. maximal_ideal R m1")
 apply (subgoal_tac "\<forall>m1. maximal_ideal R m1 \<longrightarrow> x \<in> carrier R")
 apply blast apply (rule allI) apply (rule impI)
 apply (subgoal_tac "ideal R m1") apply (subgoal_tac "x \<in> m1")
 apply (simp add: ideal_subset)
 apply (simp add:J_rad_def)
 apply (simp add:maximal_ideal_def)
apply (simp add:id_maximal_Exist)
apply assumption
done

section "6. Operation of ideals"

lemma ideal_sumTr1:"\<lbrakk> ring R; ideal R A; ideal R B \<rbrakk> \<Longrightarrow> 
   A \<^bold>+\<^sub>R B = \<Inter> {J. ideal R J \<and> (A \<union> B) \<subseteq> J}"
apply (rule equalityI)
  (* A \<^bold>+\<^sub>R B \<subseteq> \<Inter>{J. ideal R J \<and> A \<union> B \<subseteq> J} *)
apply (rule subsetI)
 apply (simp add:asettOp_def settOp_def)
 apply (frule ring_is_ag[of "R"])
 apply (frule agop_gop[of "R"])
 apply simp
apply (rule allI) apply (rule impI)
apply (subgoal_tac "\<forall>a\<in>A. \<forall>b\<in>B.  a +\<^sub>R b = x \<longrightarrow> x \<in> xa")
 apply blast apply (thin_tac "\<exists>xa\<in>A. \<exists>y\<in>B.  xa +\<^sub>R y = x")
 apply (rule ballI)+ apply (rule impI)
 apply (erule conjE)
apply (subgoal_tac "x = a +\<^sub>R b") apply (thin_tac "a +\<^sub>R b = x")
 apply simp
apply (rule ideal_pOp_closed, assumption+)
 apply (fast)
 apply (fast)
apply (rule sym, assumption)
 (* \<Inter>{J. ideal R J \<and> A \<union> B \<subseteq> J} \<subseteq> A \<^bold>+\<^sub>R B *)
apply (rule subsetI)
 apply (simp add:asettOp_def settOp_def)
 apply (frule ring_is_ag [of "R"])
 apply (frule agop_gop[of "R"])
apply (subgoal_tac "x \<in> A \<^bold>+\<^sub>R B")
apply (simp add:asettOp_def settOp_def)
apply (subgoal_tac "ideal R (A \<^bold>+\<^sub>R B) \<and> A \<union> B \<subseteq> (A \<^bold>+\<^sub>R B)")
apply (rotate_tac 5) apply simp
apply (rule conjI)
apply (simp add:sum_ideals)
 apply (thin_tac "\<forall>xa. ideal R xa \<and> A \<subseteq> xa \<and> B \<subseteq> xa \<longrightarrow> x \<in> xa")
 apply (thin_tac "GroupType.tOp (b_ag R) = pOp R")
apply (rule subsetI)
apply (simp add:Un_def)
apply (case_tac "xa \<in> A")
apply (subgoal_tac "A \<subseteq> A \<^bold>+\<^sub>R B")
 apply (rule subsetD, assumption+) 
 apply (rule sum_ideals_la1, assumption+) apply simp
apply (subgoal_tac "B \<subseteq> A \<^bold>+\<^sub>R B") apply (rule subsetD, assumption+)
 apply (simp add:sum_ideals_la2)
done

lemma sum_ideals_commute:"\<lbrakk> ring R; ideal R A; ideal R B \<rbrakk> \<Longrightarrow> 
                  A \<^bold>+\<^sub>R B = B \<^bold>+\<^sub>R A"
apply (frule ideal_sumTr1 [of "R" "B"], assumption+)
apply (frule ideal_sumTr1 [of "R" "A" "B"], assumption+)
apply (subgoal_tac "\<Inter>{J. ideal R J \<and> B \<union> A \<subseteq> J} = 
                         \<Inter>{J. ideal R J \<and> A \<union> B \<subseteq> J}")
apply blast 
apply (subgoal_tac "B \<union> A = A \<union> B")  apply simp
apply auto
done

lemma cont_ideal_prod:"\<lbrakk> ring R; ideal R A; ideal R B; ideal R C;
 A \<subseteq> C; B \<subseteq> C \<rbrakk> \<Longrightarrow> A \<diamondsuit>\<^sub>R B \<subseteq> C"
apply (simp add:ideal_prod_def)
apply (rule subsetI)
apply (subgoal_tac "C \<in> {K. ideal R K \<and> {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> K}")
apply blast apply (thin_tac "x \<in> \<Inter>{K. ideal R K \<and> 
                                {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> K}")
apply (simp add:CollectI)
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac " \<forall>i\<in>A. \<forall>j\<in>B. x =  i \<cdot>\<^sub>R j \<longrightarrow> x \<in> C") apply blast
apply (thin_tac " \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j")
apply (rule ballI)+ apply (rule impI)
apply (frule subsetD, assumption+) apply (thin_tac "i \<in> A")
apply (frule subsetD, assumption+) apply simp apply (thin_tac "j \<in> B")
 apply (thin_tac "ideal R A") apply (thin_tac "ideal R B")
apply (frule ideal_subset, assumption+)
apply (simp add:ideal_ring_multiple)
done

lemma ideal_distrib:"\<lbrakk>ring R; ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
                             A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C) =  A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R  A \<diamondsuit>\<^sub>R C"
apply (rule equalityI)
prefer 2
apply (subgoal_tac " A \<diamondsuit>\<^sub>R B \<subseteq>  A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C)")
apply (subgoal_tac "A \<diamondsuit>\<^sub>R C \<subseteq>  A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C)")
apply (rule sum_ideals_cont, assumption+)
 apply (simp add:ideal_prod_ideal)+
 apply (rule ideal_prod_ideal, assumption+)
 apply (simp add:sum_ideals)
 apply (rule subsetI)
 apply (rule subsetD, assumption+)
  apply (thin_tac "A \<diamondsuit>\<^sub>R B \<subseteq> A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C)")
  (** A \<diamondsuit>\<^sub>R C \<subseteq> A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C) **)
apply (rule subsetI) apply (simp add:ideal_prod_def)
apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j\<in>C. x =  i \<cdot>\<^sub>R j} \<subseteq> 
                      {x. \<exists>i\<in>A. \<exists>j\<in>B \<^bold>+\<^sub>R C. x =  i \<cdot>\<^sub>R j}")
apply blast
 apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>A. \<exists>j\<in>C. x =  i \<cdot>\<^sub>R j} \<subseteq> xa
                                                 \<longrightarrow> x \<in> xa")
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>C. xa =  i \<cdot>\<^sub>R j \<longrightarrow> 
                           (\<exists>i\<in>A. \<exists>j\<in>B \<^bold>+\<^sub>R C. xa =  i \<cdot>\<^sub>R j)")
apply blast
apply (thin_tac " \<exists>i\<in>A. \<exists>j\<in>C. xa =  i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (subgoal_tac "j \<in> (B \<^bold>+\<^sub>R C)") apply blast
apply (subgoal_tac "C \<subseteq>  B \<^bold>+\<^sub>R C") apply (rule subsetD, assumption+)
apply (rule sum_ideals_la2, assumption+)
  (** A \<diamondsuit>\<^sub>R B \<subseteq> A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C) **)
apply (rule subsetI) apply (simp add:ideal_prod_def)
apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> 
                      {x. \<exists>i\<in>A. \<exists>j\<in>B \<^bold>+\<^sub>R C. x =  i \<cdot>\<^sub>R j}")
apply blast
 apply (thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> xa
                                                 \<longrightarrow> x \<in> xa")
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>B. xa =  i \<cdot>\<^sub>R j \<longrightarrow> 
                           (\<exists>i\<in>A. \<exists>j\<in>B \<^bold>+\<^sub>R C. xa =  i \<cdot>\<^sub>R j)")
apply blast
apply (thin_tac " \<exists>i\<in>A. \<exists>j\<in>B. xa =  i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (subgoal_tac "j \<in> (B \<^bold>+\<^sub>R C)") apply blast
apply (subgoal_tac "B \<subseteq>  B \<^bold>+\<^sub>R C") apply (rule subsetD, assumption+)
apply (rule sum_ideals_la1, assumption+)
  (** A \<diamondsuit>\<^sub>R (B \<^bold>+\<^sub>R C) \<subseteq> A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C **)
apply (rule subsetI)
apply (simp add:ideal_prod_def asettOp_def settOp_def)
apply (rename_tac d) apply (frule ring_is_ag[of "R"])
apply (frule agop_gop[of "R"])
apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and> x =  i \<cdot>\<^sub>R j}
  = {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z = a \<cdot>\<^sub>R b +\<^sub>R a \<cdot>\<^sub>R c}") apply simp
apply (thin_tac "{x. \<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and> x =  i \<cdot>\<^sub>R j} =
           {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z =   a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c}")

apply (subgoal_tac "ideal R (A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C) \<and> 
        {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z = a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c} \<subseteq> (A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C)")
apply (subgoal_tac "d \<in>  A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C")
apply (thin_tac "\<forall>x. ideal R x \<and> {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z = a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c}
 \<subseteq> x \<longrightarrow> d \<in> x")
apply (thin_tac "ideal R (A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C) \<and> {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z =
  a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c} \<subseteq> A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C")
apply (simp add:asettOp_def settOp_def)
apply (unfold ideal_prod_def) apply simp
 apply (fold ideal_prod_def) apply simp
apply (rule conjI)
apply (rule sum_ideals, assumption+)
 apply (simp add:ideal_prod_ideal)+
 apply (rule subsetI) apply (simp add:CollectI)
 apply (thin_tac "\<forall>x. ideal R x \<and> {z. \<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. z=a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c}
  \<subseteq> x \<longrightarrow> d \<in> x")
apply (subgoal_tac "\<forall>a\<in>A. \<forall>b\<in>B. \<forall>c\<in>C. x = a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c \<longrightarrow>
                                                x \<in> A \<diamondsuit>\<^sub>R B \<^bold>+\<^sub>R A \<diamondsuit>\<^sub>R C")
apply blast apply (thin_tac "\<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. x =   a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c")
apply (rule ballI) apply (rule ballI) apply (rule ballI)
apply (rule impI) 
apply simp
apply (simp add:asettOp_def settOp_def)
 apply (subgoal_tac "a \<cdot>\<^sub>R b \<in> A \<diamondsuit>\<^sub>R B")
 apply (subgoal_tac "a \<cdot>\<^sub>R c \<in> A \<diamondsuit>\<^sub>R C") apply blast
 apply (thin_tac "a \<cdot>\<^sub>R b \<in> A \<diamondsuit>\<^sub>R B")
 apply (simp add:ideal_prod_def)
 apply (rule allI) apply (rule impI) 
 apply (erule conjE)
  apply (subgoal_tac "a \<cdot>\<^sub>R c \<in>  {x. \<exists>i\<in>A. \<exists>j\<in>C. x =  i \<cdot>\<^sub>R j}")
  apply (rule subsetD, assumption+)
  apply (thin_tac "{x. \<exists>i\<in>A. \<exists>j\<in>C. x =  i \<cdot>\<^sub>R j} \<subseteq> xa")
  apply (thin_tac "x = a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c")
 apply (simp add:CollectI) apply blast
  apply (thin_tac "x = a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c")
 apply (simp add:ideal_prod_def)
 apply (rule allI) apply (rule impI) 
  apply (erule conjE)
  apply (subgoal_tac "a \<cdot>\<^sub>R b \<in>  {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j}")
  apply (rule subsetD, assumption+)
  apply (thin_tac "{x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} \<subseteq> x")
 apply (simp add:CollectI) apply blast

apply (thin_tac "\<forall>x. ideal R x \<and> {x. \<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C. GroupType.tOp (b_ag R) x y = j) \<and> x = RingType.tOp R i j} \<subseteq> x \<longrightarrow> d \<in> x")
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>A. \<forall>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and> x =  i \<cdot>\<^sub>R j \<longrightarrow>
           (\<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. x =   a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c)")
 apply blast apply (thin_tac "\<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and> x = 
                                                             i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule allI) apply (rule impI) 
 apply (erule conjE)
apply (rename_tac d)
apply (subgoal_tac "\<forall>b\<in>B. \<forall>c\<in>C.  b +\<^sub>R c = d \<longrightarrow> x = i \<cdot>\<^sub>R b +\<^sub>R i \<cdot>\<^sub>R c")
apply blast apply (thin_tac "\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = d")
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (subgoal_tac "d = b +\<^sub>R c") apply (thin_tac "b +\<^sub>R c = d")
apply simp
apply (rule ring_distrib1, assumption+) 
 apply (simp add:ideal_subset)+

apply (rule subsetI)
 apply (simp add:CollectI)
 apply (rename_tac d)
apply (subgoal_tac "\<forall>a\<in>A. \<forall>b\<in>B. \<forall>c\<in>C. d =   a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c \<longrightarrow>
               (\<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and> d =  i \<cdot>\<^sub>R j)")
apply blast apply (thin_tac "\<exists>a\<in>A. \<exists>b\<in>B. \<exists>c\<in>C. d =   a \<cdot>\<^sub>R b +\<^sub>R  a \<cdot>\<^sub>R c")
apply (rule ballI) apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (frule ideal_subset, assumption+)
apply (subgoal_tac "b \<in> carrier R")
apply (subgoal_tac "c \<in> carrier R")
apply (simp  add:ring_distrib1 [THEN sym])
apply (subgoal_tac "\<forall>a\<in>A. \<forall>i\<in>A.\<forall>j. a = i \<and> (b +\<^sub>R c = j) \<longrightarrow> 
    (\<exists>i\<in>A. \<exists>j. (\<exists>x\<in>B. \<exists>y\<in>C.  x +\<^sub>R y = j) \<and>  a \<cdot>\<^sub>R ( b +\<^sub>R c) =  i \<cdot>\<^sub>R j)")
 apply blast
apply (rule ballI) apply (rule ballI) apply (rule allI) apply (rule impI)
 apply (erule conjE)
apply (subgoal_tac "i= aa") apply (thin_tac " aa = i")
apply (subgoal_tac "j =  b +\<^sub>R c")  apply (thin_tac " b +\<^sub>R c = j")
apply blast
apply (rule sym, assumption)
apply (rule sym, assumption)
apply (simp add:ideal_subset) apply (simp add:ideal_subset)
done

lemma id_coprimeTr0:"\<lbrakk> ring R; ideal R A \<rbrakk> \<Longrightarrow> (carrier R) \<diamondsuit>\<^sub>R A = A"  
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ideal_prod_def)
 apply (rename_tac d)
apply (subgoal_tac "{x. \<exists>i\<in>carrier R. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq> A")
apply simp
 apply (thin_tac "\<forall>x. ideal R x \<and> {x. \<exists>i\<in>carrier R. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq> x \<longrightarrow>  d \<in> x")
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>carrier R. \<forall>j\<in>A. x =  i \<cdot>\<^sub>R j \<longrightarrow> x \<in> A")
 apply blast apply (thin_tac "\<exists>i\<in>carrier R. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (simp add:ideal_ring_multiple)

apply (simp add:ideal_prod_def)
apply (rule subsetI) apply (simp add:CollectI)
apply (rule allI) apply (rule impI)
apply (erule conjE) 
apply (subgoal_tac "x \<in> {x. \<exists>i\<in>carrier R. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j}")
apply (rule subsetD, assumption+)
 apply (thin_tac "{x. \<exists>i\<in>carrier R. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq> xa")
apply (simp add:CollectI)
apply (subgoal_tac "1\<^sub>R \<in> carrier R")
apply (subgoal_tac "x = 1\<^sub>R \<cdot>\<^sub>R x") apply blast
apply (subst ring_tOp_commute, assumption+)
 apply (simp add:ideal_subset) apply (rule ring_r_one[THEN sym], assumption)
 apply (simp add:ideal_subset)
apply (simp add:ring_def)
done

lemma prod_commute:"\<lbrakk> ring R; ideal R A; ideal R B \<rbrakk> \<Longrightarrow>
         A \<diamondsuit>\<^sub>R B = B \<diamondsuit>\<^sub>R A"
apply (simp add:ideal_prod_def)
apply (subgoal_tac "{x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} = 
               {x. \<exists>i\<in>B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j}")
apply simp
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>A. \<forall>j\<in>B. x =  i \<cdot>\<^sub>R j \<longrightarrow> (\<exists>i\<in>B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j)")
apply blast apply (thin_tac "\<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule ballI) apply (rule impI) 
apply (frule ideal_subset, assumption+)        
apply (rotate_tac 2) apply (frule ideal_subset, assumption+)
apply (subgoal_tac "x = j \<cdot>\<^sub>R i") apply (thin_tac "x =  i \<cdot>\<^sub>R j")
apply blast
apply (simp add:ring_tOp_commute)
 (** {x. \<exists>i\<in>B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j} \<subseteq> {x. \<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j} **)
apply (rule subsetI) apply (simp add:CollectI)
apply (subgoal_tac "\<forall>i\<in>B. \<forall>j\<in>A. x =  i \<cdot>\<^sub>R j \<longrightarrow> (\<exists>i\<in>A. \<exists>j\<in>B. x =  i \<cdot>\<^sub>R j)")
apply blast apply (thin_tac "\<exists>i\<in>B. \<exists>j\<in>A. x =  i \<cdot>\<^sub>R j")
apply (rule ballI) apply (rule ballI) apply (rule impI)
apply (frule ideal_subset, assumption+) apply (rotate_tac 2)
apply (frule ideal_subset, assumption+)
apply (subgoal_tac " x =  j \<cdot>\<^sub>R i") apply blast
apply (simp add:ring_tOp_commute)
done
 
end
