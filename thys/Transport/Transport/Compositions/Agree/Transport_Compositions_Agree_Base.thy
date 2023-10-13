\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Compositions With Agreeing Relations\<close>
subsection \<open>Basic Setup\<close>
theory Transport_Compositions_Agree_Base
  imports
    Transport_Base
begin

locale transport_comp_agree =
  g1 : galois L1 R1 l1 r1 + g2 : galois L2 R2 l2 r2
  for L1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R1 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l1 :: "'a \<Rightarrow> 'b"
  and r1 :: "'b \<Rightarrow> 'a"
  and L2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and R2 :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and l2 :: "'b \<Rightarrow> 'c"
  and r2 :: "'c \<Rightarrow> 'b"
begin

text \<open>This locale collects results about the composition of transportable
components under the assumption that the relations @{term "R1"} and
@{term "L2"} agree (in one sense or another) whenever required. Such an
agreement may not necessarily hold in practice, and the resulting theorems are
not particularly pretty. However, in the special case where @{term "R1 = L2"},
most side-conditions disappear and the results are very simple.\<close>

notation L1 (infix "\<le>\<^bsub>L1\<^esub>" 50)
notation R1 (infix "\<le>\<^bsub>R1\<^esub>" 50)
notation L2 (infix "\<le>\<^bsub>L2\<^esub>" 50)
notation R2 (infix "\<le>\<^bsub>R2\<^esub>" 50)

notation g1.ge_left (infix "\<ge>\<^bsub>L1\<^esub>" 50)
notation g1.ge_right (infix "\<ge>\<^bsub>R1\<^esub>" 50)
notation g2.ge_left (infix "\<ge>\<^bsub>L2\<^esub>" 50)
notation g2.ge_right (infix "\<ge>\<^bsub>R2\<^esub>" 50)

notation g1.left_Galois (infix "\<^bsub>L1\<^esub>\<lessapprox>" 50)
notation g1.right_Galois (infix "\<^bsub>R1\<^esub>\<lessapprox>" 50)
notation g2.left_Galois (infix "\<^bsub>L2\<^esub>\<lessapprox>" 50)
notation g2.right_Galois (infix "\<^bsub>R2\<^esub>\<lessapprox>" 50)

notation g1.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L1\<^esub>" 50)
notation g1.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R1\<^esub>" 50)
notation g2.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L2\<^esub>" 50)
notation g2.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R2\<^esub>" 50)

notation g1.right_ge_Galois (infix "\<^bsub>R1\<^esub>\<greaterapprox>" 50)
notation g1.Galois_right (infix "\<lessapprox>\<^bsub>R1\<^esub>" 50)
notation g2.right_ge_Galois (infix "\<^bsub>R2\<^esub>\<greaterapprox>" 50)
notation g2.Galois_right (infix "\<lessapprox>\<^bsub>R2\<^esub>" 50)

notation g1.left_ge_Galois (infix "\<^bsub>L1\<^esub>\<greaterapprox>" 50)
notation g1.Galois_left (infix "\<lessapprox>\<^bsub>L1\<^esub>" 50)
notation g2.left_ge_Galois (infix "\<^bsub>L2\<^esub>\<greaterapprox>" 50)
notation g2.Galois_left (infix "\<lessapprox>\<^bsub>L2\<^esub>" 50)

notation g1.unit ("\<eta>\<^sub>1")
notation g1.counit ("\<epsilon>\<^sub>1")
notation g2.unit ("\<eta>\<^sub>2")
notation g2.counit ("\<epsilon>\<^sub>2")

abbreviation (input) "L \<equiv> L1"

definition "l \<equiv> l2 \<circ> l1"

lemma left_eq_comp: "l = l2 \<circ> l1"
  unfolding l_def ..

lemma left_eq [simp]: "l x = l2 (l1 x)"
  unfolding left_eq_comp by simp

context
begin

interpretation flip : transport_comp_agree R2 L2 r2 l2 R1 L1 r1 l1 .

abbreviation (input) "R \<equiv> flip.L"
abbreviation "r \<equiv> flip.l"

lemma right_eq_comp: "r = r1 \<circ> r2"
  unfolding flip.l_def ..

lemma right_eq [simp]: "r z = r1 (r2 z)"
  unfolding right_eq_comp by simp

lemmas transport_defs = left_eq_comp right_eq_comp

end

sublocale transport L R l r .

(*FIXME: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

end

locale transport_comp_same =
  transport_comp_agree L1 R1 l1 r1 R1 R2 l2 r2
  for L1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R1 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l1 :: "'a \<Rightarrow> 'b"
  and r1 :: "'b \<Rightarrow> 'a"
  and R2 :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and l2 :: "'b \<Rightarrow> 'c"
  and r2 :: "'c \<Rightarrow> 'b"
begin

text \<open>This locale is a special case of @{locale "transport_comp_agree"} where
the left and right components both use @{term "(\<le>\<^bsub>R1\<^esub>)"} as their right and left
relation, respectively. This is the special case that is most prominent in the
literature. The resulting theorems are quite simple, but often not applicable
in practice.\<close>

end


end