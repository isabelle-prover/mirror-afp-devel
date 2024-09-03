(* Formalization adapted from: 
   Fabián Fernando Serrano Suárez, "Formalización en Isar de la
   Meta-Lógica de Primer Orden." PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidad de Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory BinaryTreeEnumeration
imports MaximalHintikka 
begin
(*>*)

lemma enumeration: "enumeration f = (\<exists>g. \<forall>y. f(g y) = y)"
  by (metis enumeration_def)


datatype tree_b = Leaf nat | Tree tree_b tree_b

primrec diag :: "nat \<Rightarrow> (nat \<times> nat)" where
  "diag 0 = (0, 0)"
| "diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))"


function undiag :: "nat \<times> nat \<Rightarrow> nat" where
  "undiag (0, 0) = 0"
| "undiag (0, Suc y) = Suc (undiag (y, 0))"
| "undiag (Suc x, y) = Suc (undiag (x, Suc y))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)") auto


lemma diag_undiag [simp]: "diag (undiag (x, y)) = (x, y)"
by (rule undiag.induct) (simp add: Let_def)+


lemma enumeration_natxnat: "enumeration (diag::nat \<Rightarrow> (nat \<times> nat))"
proof -
  have "\<forall>x y. diag (undiag (x, y)) = (x, y)" using diag_undiag by auto
  hence "\<exists>undiag. \<forall>x y. diag (undiag (x, y)) = (x, y)" by blast
  thus ?thesis using enumeration[of diag] by auto
qed


function diag_tree_b :: "nat \<Rightarrow> tree_b" where
"diag_tree_b n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
      | Suc z \<Rightarrow> Tree (diag_tree_b z) (diag_tree_b (snd (diag n))))"
by auto

(*<*)

(*>*)

(*<*)
lemma diag_le1: "fst (diag (Suc n)) < Suc n"
by (induct n) (simp_all add: Let_def split_def split: nat.split) 

lemma diag_le2: "snd (diag (Suc (Suc n))) < Suc (Suc n)"
using diag_le1 by (induct n) (simp_all add: Let_def split_def split: nat.split) 

lemma diag_le3:
  assumes "fst (diag n) = Suc x"
  shows "snd (diag n) < n"
proof (cases n) 
  assume "n=0" thus "snd (diag n) < n" using assms by simp
next
  fix nat
  assume h1: "n = Suc nat"
  show "snd (diag n) < n"
  proof (cases nat)
    assume "nat = 0"
    thus "snd (diag n) < n" using assms h1 by (simp add: Let_def)
  next 
    fix nata
    assume "nat = Suc nata"
    thus "snd (diag n) < n" using assms h1 by hypsubst (rule diag_le2)
  qed
qed

lemma diag_le4: 
  assumes "fst (diag n) = Suc x"
  shows "x < n"
proof (cases n)  
  assume "n = 0" thus "x < n" using assms by simp
next
  fix nat
  assume h1: "n = Suc nat" 
  show "x < n"
  proof (cases nat)
    assume "nat = 0" thus "x < n" using assms h1 by hypsubst (simp add: Let_def)
  next
    fix nata
    assume h2: "nat = Suc nata"
    hence "fst(diag n) = fst(diag (Suc(Suc nata)))" using h1 by simp
    hence "fst(diag (Suc(Suc nata))) = Suc x" using assms by simp
    moreover
    have "fst(diag (Suc(Suc nata))) < Suc(Suc nata)" by (rule diag_le1)
    ultimately
    have "Suc x < Suc (Suc nata)" by simp
    thus "x < n" using h1 h2 by simp
  qed
qed

termination diag_tree_b
by (relation "measure (\<lambda>x. x)") (auto intro: diag_le3 diag_le4)
(*>*)


primrec undiag_tree_b :: "tree_b \<Rightarrow> nat" where
  "undiag_tree_b (Leaf n) = undiag (0, n)"
| "undiag_tree_b (Tree t1 t2) =
   undiag (Suc (undiag_tree_b t1), undiag_tree_b t2)"


lemma diag_undiag_tree_b [simp]: "diag_tree_b (undiag_tree_b t) = t"
by (induct t) (simp_all add: Let_def)


lemma enumeration_tree_b: "enumeration (diag_tree_b :: nat \<Rightarrow> tree_b)"
proof - 
  have "\<forall>x. diag_tree_b (undiag_tree_b x) = x" 
    using diag_undiag_tree_b by blast
  hence "\<exists>undiag_tree_b. \<forall>x . diag_tree_b (undiag_tree_b x) = x" by blast
  thus ?thesis using enumeration[of diag_tree_b] by auto
qed

(*<*)
declare diag_tree_b.simps [simp del] undiag_tree_b.simps [simp del]
(*>*)

(*<*)
end
(*>*)