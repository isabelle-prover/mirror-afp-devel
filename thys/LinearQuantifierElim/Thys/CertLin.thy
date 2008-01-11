(*  ID:         $Id: CertLin.thy,v 1.2 2008-01-11 15:22:14 lsf37 Exp $
    Author:     Tobias Nipkow, 2007

A simple certificate checker for q-free linear arithmetic:
is linear combination of atoms and certificate contradictory?
*)

theory CertLin
imports LinArith
begin

fun pls_atom :: "atom \<Rightarrow> atom \<Rightarrow> atom" where
"pls_atom (Eq r\<^isub>1 cs\<^isub>1) (Eq r\<^isub>2 cs\<^isub>2) = Eq (r\<^isub>1+r\<^isub>2) (cs\<^isub>1+cs\<^isub>2)" |
"pls_atom (Eq r\<^isub>1 cs\<^isub>1) (Less r\<^isub>2 cs\<^isub>2) = Less (r\<^isub>1+r\<^isub>2) (cs\<^isub>1+cs\<^isub>2)" |
"pls_atom (Less r\<^isub>1 cs\<^isub>1) (Eq r\<^isub>2 cs\<^isub>2) = Less (r\<^isub>1+r\<^isub>2) (cs\<^isub>1+cs\<^isub>2)" |
"pls_atom (Less r\<^isub>1 cs\<^isub>1) (Less r\<^isub>2 cs\<^isub>2) = Less (r\<^isub>1+r\<^isub>2) (cs\<^isub>1+cs\<^isub>2)"

declare list_add_assoc[simp]

instance atom :: plus plus_atom_def: "op + == pls_atom" ..
instance atom :: zero zero_atom_def: "0 == Eq 0 []" ..
instance atom :: monoid_add
apply intro_classes
apply(simp_all add:plus_atom_def zero_atom_def)
apply(case_tac a)
apply(case_tac b)
apply(case_tac c)
apply simp_all
apply(case_tac c)
apply simp_all
apply(case_tac b)
apply(case_tac c)
apply simp_all
apply(case_tac c)
apply simp_all
apply(case_tac a)
apply simp_all
apply(case_tac a)
apply simp_all
done

lemma I_R_additive: "I\<^isub>R a xs \<Longrightarrow> I\<^isub>R b xs \<Longrightarrow> I\<^isub>R(a+b) xs"
apply(simp add:plus_atom_def)
apply(case_tac a)
apply(case_tac b)
apply (simp_all add:iprod_left_add_distrib)
apply(case_tac b)
apply (simp_all add:iprod_left_add_distrib)
done

fun mult_atom :: "real \<Rightarrow> atom \<Rightarrow> atom" (infix "*\<^sub>a" 70) where
"c *\<^sub>a Eq r cs = Eq (c*r) (c *\<^sub>s cs)" |
"c *\<^sub>a Less r cs = (if c=0 then Eq 0 [] else Less (c*r) (c *\<^sub>s cs))"

definition iprod_a :: "real list \<Rightarrow> atom list \<Rightarrow> atom" (infix "\<odot>\<^sub>a" 70)
where "cs \<odot>\<^sub>a as = (\<Sum>(c,a) \<leftarrow> zip cs as. c *\<^sub>a a)"

lemma iprod_a_Nil2[simp]: "cs \<odot>\<^sub>a [] = 0"
by(simp add:iprod_a_def)

lemma [simp]: "(c#cs) \<odot>\<^sub>a (a#as) = (c *\<^sub>a a) + cs \<odot>\<^sub>a as"
by(simp add:iprod_a_def)

definition contradict :: "atom list \<Rightarrow> real list \<Rightarrow> bool" where
"contradict as cs \<longleftrightarrow> size cs = size as \<and> (\<forall>c\<in>set cs. c\<ge>0) \<and>
  (case cs \<odot>\<^sub>a as of Eq r cs \<Rightarrow> r \<noteq> 0 \<and> (\<forall>c\<in>set cs. c=0)
                  | Less r cs \<Rightarrow> r \<ge> 0 \<and> (\<forall>c\<in>set cs. c=0))"

definition
"contradict_dnf ass = (EX css. list_all2 contradict ass css)"

lemma refute_I:
  "~ Logic.interpret h (Neg f) e \<Longrightarrow> Logic.interpret h f e"
by simp

lemma I_R_mult_atom: "c \<ge> 0 \<Longrightarrow> I\<^isub>R a xs \<Longrightarrow> I\<^isub>R (c *\<^sub>a a) xs"
apply(cases a)
 apply(clarsimp simp:iprod_assoc)
 apply(rule real_mult_less_mono2)
  apply arith
 apply simp
apply(simp add:iprod_assoc)
done

lemma I_R_iprod_a:
 "size cs = size as \<Longrightarrow> \<forall>(c,a) \<in> set(zip cs as). I\<^isub>R (c *\<^sub>a a) xs
 \<Longrightarrow> I\<^isub>R (cs \<odot>\<^sub>a as) xs"
apply(induct cs as rule:list_induct2)
 apply (simp add:zero_atom_def)
apply(simp add:I_R_additive)
done

lemma contradictD:
 "contradict as cs \<Longrightarrow> \<exists>a\<in>set as. \<not> I\<^isub>R a xs"
proof -
  assume "contradict as cs"
  have "\<not> I\<^isub>R (cs \<odot>\<^sub>a as) xs"
  proof (cases "cs \<odot>\<^sub>a as")
    case Less thus ?thesis using `contradict as cs`
      by(simp add:contradict_def iprod0_if_coeffs0)
  next
    case Eq thus ?thesis using `contradict as cs`
      by(simp add:contradict_def iprod0_if_coeffs0)
  qed
  thus ?thesis using `contradict as cs`
    by(force simp add:contradict_def intro: I_R_iprod_a I_R_mult_atom
             elim:in_set_zipE)
qed

lemma cyclic_dnfD: "qfree f \<Longrightarrow> contradict_dnf (dnf(R.nnf f)) \<Longrightarrow> ~R.I f xs"
apply(subst R.I_nnf[symmetric])
apply(subst R.I_dnf[symmetric])
apply(erule R.nqfree_nnf)
apply(auto simp add:contradict_dnf_def list_all2_def in_set_conv_nth)
apply(drule_tac x="(dnf(R.nnf f) ! i, css!i)" in bspec)
apply (auto simp:set_zip)
apply(drule_tac xs=xs in contradictD)
apply auto
done

end