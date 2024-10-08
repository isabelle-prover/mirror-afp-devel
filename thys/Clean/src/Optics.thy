text\<open>This is an excerpt of the Optics library 
     \<^url>\<open>https://www.isa-afp.org/entries/Optics.html\<close> by Frank Zeyda and
     Simon Foster. It provides a rich infrastructure for \<^emph>\<open>algebraic lenses\<close>,
     an abstract theory allowing to describe parts of memory and their 
     independence. We use it to abstractly model typed program variables and
     framing conditions. 

     Optics provides a rich framework for lense compositions and sub-lenses
     which we will not use in the context of Clean; even the offered concept
     of a list-lense, a possible means to model the stack-infrastructure 
     required for local variables, is actually richer than needed.

     Since Clean strives for minimality, we restrict ourselves to this "proxy"
     theory for Optics.
\<close>

theory Optics
  imports Lens_Laws
begin


fun      upd_hd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" 
  where "upd_hd f [] = []"
      | "upd_hd f (a#S) = f a # S"

lemma [simp] :"tl (upd_hd f S) = tl S" 
  by (metis list.sel(3) upd_hd.elims)


definition upd2put :: "(('d \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where   "upd2put f = (\<lambda>\<sigma>. \<lambda> b. f (\<lambda>_. b) \<sigma>)"

definition create\<^sub>L 
  where "create\<^sub>L getv updv = \<lparr>lens_get = getv,lens_put = upd2put updv\<rparr>"

definition "hd\<^sub>L = create\<^sub>L hd upd_hd"   (* works since no partial lenses needed in Clean*)

definition "map_nth i = (\<lambda>f l. list_update l i (f (l ! i)))"


find_theorems "list_update"


lemma [simp]: "map_nth i f [] = []"
  by(simp_all add: map_nth_def)

lemma [simp]: "map_nth i f (a#R) = (case i of 0 \<Rightarrow> (f a) # R | Suc j \<Rightarrow> a # map_nth j f R)"
  by(simp add: Nitpick.case_nat_unfold map_nth_def)

lemma [simp]: "map_nth n (\<lambda>x. x) S = S"
  by(induct S, simp_all add: map_nth_def)
 
lemma [simp]: "length(map_nth n f S) = length S"
  by(simp add: map_nth_def)

lemma [simp]: "n < length S \<Longrightarrow> (map_nth n f S) ! n = f (S ! n)"
  by (simp add: map_nth_def)

lemma [simp]: "n < length S \<Longrightarrow> m < length S \<Longrightarrow> n\<noteq>m \<Longrightarrow> (map_nth m f S) ! n = S ! n"
  by (simp add: map_nth_def)

lemma [simp]: "n < length S \<Longrightarrow> (map_nth n f (map_nth n g S)) = (map_nth n (f o g) S)"
  by (simp add: map_nth_def)

(* and more *)

lemma indep_list_lift : 
     "X \<bowtie> create\<^sub>L getv updv 
      \<Longrightarrow> (\<lambda>f \<sigma>. updv (\<lambda>_. f (getv \<sigma>)) \<sigma>) = updv 
      \<Longrightarrow> X \<bowtie> create\<^sub>L (hd \<circ> getv ) (updv \<circ> upd_hd)"
  unfolding create\<^sub>L_def o_def Lens_Laws.lens_indep_def upd2put_def
  by (auto,metis (no_types)) (metis (no_types))

end