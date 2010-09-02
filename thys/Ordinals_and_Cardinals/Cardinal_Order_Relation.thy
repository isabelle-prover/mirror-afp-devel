header {* Cardinal-order relations  *}

(* author: Andrei Popescu *)

theory Cardinal_Order_Relation imports Infinite_Set Constructions_on_Wellorders 
begin


text{* In this section, we define cardinal-order relations to be minim well-orders 
on their field.  Then we define the cardinal of a set to be {\em some} cardinal-order 
relation on that set, which will be unique up to order isomorphism.  Then we study 
the connection between cardinals and:
\begin{itemize}
\item standard set-theoretic constructions: products, 
sums, unions, lists, powersets, set-of finite sets operator;
\item finiteness and infiniteness (in particular, with the numeric cardinal operator 
for finite sets, @{text "card"}, from the theory @{text "Finite_Sets.thy"}).  
\end{itemize}
%
On the way, we define the canonical $\omega$ cardinal and finite cardinals.  We also 
define (again, up to order isomorphism) the successor of a cardinal, and show that 
any cardinal admits a successor.   

Main results of this section are the existence of cardinal relations and the 
facts that, in the presence of infiniteness, 
most of the standard set-theoretic constructions (except for the powerset) 
{\em do not increase cardinality}.  In particular, e.g., the set of words/lists over 
any infinite set has the same cardinality (hence, is in bijection) with that set.  
*} 


subsection {* Cardinal orders *}


text{* A cardinal order in our setting shall be a well-order {\em minim} w.r.t. the 
order-embedding relation, @{text "\<le>o"} (which is the same as being {\em minimal} w.r.t. the 
strict order-embedding relation, @{text "<o"}), among all the well-orders on its field.  *}   

definition card_order_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
where 
"card_order_on A r \<equiv> well_order_on A r \<and> (\<forall>r'. well_order_on A r' \<longrightarrow> r \<le>o r')"


abbreviation "Card_order r \<equiv> card_order_on (Field r) r"
abbreviation "card_order r \<equiv> card_order_on UNIV r"


lemma card_order_on_Card_order:
"card_order_on A r \<Longrightarrow> A = Field r \<and> Card_order r"
unfolding card_order_on_def using rel.well_order_on_Field by blast


text{* The existence of a cardinal relation on any given set (which will mean 
that any set has a cardinal) follows from two facts: 
\begin{itemize}
\item Zermelo's theorem (proved in @{text "Zorn.thy"} as theorem @{text "well_order_on"}), 
which states that on any given set there exists a well-order;
\item The well-founded-ness of @{text "<o"}, ensuring that then there exists a minimal 
such well-order, i.e., a cardinal order.  
\end{itemize}
*}


theorem card_order_on: "\<exists>r. card_order_on A r"
proof-
  obtain R where R_def: "R = {r. well_order_on A r}" by blast
  have 1: "R \<noteq> {} \<and> (\<forall>r \<in> R. Well_order r)" 
  using well_order_on[of A] R_def rel.well_order_on_Well_order by blast
  hence "\<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'" 
  using  exists_minim_Well_order[of R] by auto
  thus ?thesis using R_def unfolding card_order_on_def by auto
qed


lemma card_order_on_ordIso:
assumes CO: "card_order_on A r" and CO': "card_order_on A r'"
shows "r =o r'"
using assms unfolding card_order_on_def
using ordIso_iff_ordLeq by blast


lemma Card_order_ordIso:
assumes CO: "Card_order r" and ISO: "r' =o r"
shows "Card_order r'"
using ISO unfolding ordIso_def
proof(unfold card_order_on_def, auto)
  fix p' assume "well_order_on (Field r') p'"  
  hence 0: "Well_order p' \<and> Field p' = Field r'" 
  using rel.well_order_on_Well_order by blast
  obtain f where 1: "iso r' r f" and 2: "Well_order r \<and> Well_order r'" 
  using ISO unfolding ordIso_def by auto
  hence 3: "inj_on f (Field r') \<and> f ` (Field r') = Field r" 
  by (auto simp add: iso_iff embed_inj_on) 
  let ?p = "dir_image p' f"
  have 4: "p' =o ?p \<and> Well_order ?p" 
  using 0 2 3 by (auto simp add: dir_image_ordIso Well_order_dir_image)
  moreover have "Field ?p =  Field r" 
  using 0 3 by (auto simp add: dir_image_Field2 order_on_defs)
  ultimately have "well_order_on (Field r) ?p" by auto
  hence "r \<le>o ?p" using CO unfolding card_order_on_def by auto
  thus "r' \<le>o p'"
  using ISO 4 ordLeq_ordIso_trans ordIso_ordLeq_trans ordIso_symmetric by blast
qed


lemma Card_order_ordIso2:
assumes CO: "Card_order r" and ISO: "r =o r'"
shows "Card_order r'"
using assms Card_order_ordIso ordIso_symmetric by blast


subsection {* Cardinal of a set *}


text{* We define the cardinal of set to be {\em some} cardinal order on that set. 
We shall prove that this notion is unique up to order isomorphism, meaning 
that order isomorphism shall be the true identity of cardinals.  *}


definition card_of :: "'a set \<Rightarrow> 'a rel" ("|_|" )
where "card_of A = (SOME r. card_order_on A r)"


lemma card_of_card_order_on: "card_order_on A |A|"
unfolding card_of_def by (auto simp add: card_order_on someI_ex)


lemma card_of_well_order_on: "well_order_on A |A|"
using card_of_card_order_on card_order_on_def by blast


lemma Field_card_of: "Field |A| = A"
using card_of_card_order_on[of A] unfolding card_order_on_def 
using rel.well_order_on_Field by blast


lemma card_of_Card_order: "Card_order |A|"
by (auto simp add: card_of_card_order_on Field_card_of)


corollary ordIso_card_of_imp_Card_order: 
"r =o |A| \<Longrightarrow> Card_order r"
using card_of_Card_order Card_order_ordIso by blast


lemma card_of_Well_order: "Well_order |A|"
using card_of_Card_order unfolding  card_order_on_def by auto


lemma card_of_refl: "|A| =o |A|"
using card_of_Well_order ordIso_reflexive by blast


lemma card_of_least: "well_order_on A r \<Longrightarrow> |A| \<le>o r"
using card_of_card_order_on unfolding card_order_on_def by blast 


lemma card_of_ordIso: 
"(\<exists>f. bij_betw f A B) = ( |A| =o |B| )"
proof(auto)
  fix f assume *: "bij_betw f A B"
  then obtain r where "well_order_on B r \<and> |A| =o r"
  using Well_order_iso_copy card_of_well_order_on by blast
  hence "|B| \<le>o |A|" using card_of_least 
  ordLeq_ordIso_trans ordIso_symmetric by blast
  moreover 
  {let ?g = "inv_into A f" 
   have "bij_betw ?g B A" using * bij_betw_inv_into by blast
   then obtain r where "well_order_on A r \<and> |B| =o r"
   using Well_order_iso_copy card_of_well_order_on by blast
   hence "|A| \<le>o |B|" using card_of_least 
   ordLeq_ordIso_trans ordIso_symmetric by blast
  }
  ultimately show "|A| =o |B|" using ordIso_iff_ordLeq by blast
next
  assume "|A| =o |B|" 
  then obtain f where "iso |A| |B| f" 
  unfolding ordIso_def by auto
  hence "bij_betw f A B" unfolding iso_def Field_card_of by simp
  thus "\<exists>f. bij_betw f A B" by auto
qed


lemma card_of_ordLeq: 
"(\<exists>f. inj_on f A \<and> f ` A \<le> B) = ( |A| \<le>o |B| )"  
proof(auto)
  fix f assume *: "inj_on f A" and **: "f ` A \<le> B"
  {assume "|B| <o |A|" 
   hence "|B| \<le>o |A|" using ordLeq_iff_ordLess_or_ordIso by blast
   then obtain g where "embed |B| |A| g" 
   unfolding ordLeq_def by auto
   hence 1: "inj_on g B \<and> g ` B \<le> A" using embed_inj_on[of "|B|" "|A|" "g"] 
   card_of_Well_order[of "B"] Field_card_of[of "B"] Field_card_of[of "A"] 
   embed_Field[of "|B|" "|A|" g] by auto
   obtain h where "bij_betw h A B" 
   using * ** 1 Cantor_Bernstein[of f] by fastsimp
   hence "|A| =o |B|" using card_of_ordIso by blast
   hence "|A| \<le>o |B|" using ordIso_iff_ordLeq by auto
  }
  thus "|A| \<le>o |B|" using ordLess_or_ordLeq[of "|B|" "|A|"]
  by (auto simp add: card_of_Well_order)
next
  assume *: "|A| \<le>o |B|"
  obtain f where "embed |A| |B| f" 
  using * unfolding ordLeq_def by auto
  hence "inj_on f A \<and> f ` A \<le> B" using embed_inj_on[of "|A|" "|B|" f] 
  card_of_Well_order[of "A"] Field_card_of[of "A"] Field_card_of[of "B"] 
  embed_Field[of "|A|" "|B|" f] by auto
  thus "\<exists>f. inj_on f A \<and> f ` A \<le> B" by auto
qed


lemma card_of_ordLeq2: 
"A \<noteq> {} \<Longrightarrow> (\<exists>g. g ` B = A) = ( |A| \<le>o |B| )"
using card_of_ordLeq[of A B] inj_on_iff_surjective[of A B] by auto


lemma card_of_inj_rel: assumes INJ: "!! x y y'. \<lbrakk>(x,y) : R; (x,y') : R\<rbrakk> \<Longrightarrow> y = y'"
shows "|{y. EX x. (x,y) : R}| <=o |{x. EX y. (x,y) : R}|"
proof-
  let ?Y = "{y. EX x. (x,y) : R}"  let ?X = "{x. EX y. (x,y) : R}"
  let ?f = "% y. SOME x. (x,y) : R"
  have "?f ` ?Y <= ?X" using someI by force (* FIXME: takes a bit long *)
  moreover have "inj_on ?f ?Y"
  unfolding inj_on_def proof(auto)
    fix y1 x1 y2 x2
    assume *: "(x1, y1) \<in> R" "(x2, y2) \<in> R" and **: "?f y1 = ?f y2"
    hence "(?f y1,y1) : R" using someI[of "% x. (x,y1) : R"] by auto
    moreover have "(?f y2,y2) : R" using * someI[of "% x. (x,y2) : R"] by auto
    ultimately show "y1 = y2" using ** INJ by auto
  qed
  ultimately show "|?Y| <=o |?X|" using card_of_ordLeq by (auto dest: predicate1D)
qed


lemma card_of_ordLess:
"(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = ( |B| <o |A| )"  
proof-
  have "(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = (\<not> |A| \<le>o |B| )" 
  using card_of_ordLeq by blast
  also have "\<dots> = ( |B| <o |A| )" 
  using card_of_Well_order[of A] card_of_Well_order[of B]
        ordLess_iff_not_ordLeq by auto
  finally show ?thesis .
qed


lemma card_of_ordLess2:
"B \<noteq> {} \<Longrightarrow> (\<not>(\<exists>f. f ` A = B)) = ( |A| <o |B| )"
using card_of_ordLess[of B A] inj_on_iff_surjective[of B A] by auto


lemma card_of_unique: 
"card_order_on A r \<Longrightarrow> r =o |A|"
by (auto simp add: card_order_on_ordIso card_of_card_order_on)


lemma card_of_unique2: "\<lbrakk>card_order_on B r; bij_betw f A B\<rbrakk> \<Longrightarrow> r =o |A|"
using card_of_ordIso card_of_unique ordIso_equivalence by blast


lemma card_of_mono1:
"A \<le> B \<Longrightarrow> |A| \<le>o |B|"
using inj_on_id[of A] card_of_ordLeq[of A B] by fastsimp


lemma card_of_mono2: 
assumes "r \<le>o r'"
shows "|Field r| \<le>o |Field r'|"
proof-
  obtain f where 
  1: "well_order_on (Field r) r \<and> well_order_on (Field r) r \<and> embed r r' f" 
  using assms unfolding ordLeq_def 
  by (auto simp add: rel.well_order_on_Well_order)
  hence "inj_on f (Field r) \<and> f ` (Field r) \<le> Field r'" 
  by (auto simp add: embed_inj_on embed_Field)
  thus "|Field r| \<le>o |Field r'|" using card_of_ordLeq by blast
qed


lemma card_of_cong: "r =o r' \<Longrightarrow> |Field r| =o |Field r'|"
by (auto simp add: card_of_mono2 ordIso_iff_ordLeq)


lemma card_of_Field_ordLess: "Well_order r \<Longrightarrow> |Field r| \<le>o r"
using card_of_least card_of_well_order_on rel.well_order_on_Well_order by blast


lemma card_of_Field_ordIso: 
assumes "Card_order r"
shows "|Field r| =o r"
proof- 
  have "card_order_on (Field r) r"
  using assms card_order_on_Card_order by blast
  moreover have "card_order_on (Field r) |Field r|"
  using card_of_card_order_on by blast
  ultimately show ?thesis using card_order_on_ordIso by blast
qed


lemma Card_order_iff_ordIso_card_of:
"Card_order r = (r =o |Field r| )"
using ordIso_card_of_imp_Card_order card_of_Field_ordIso ordIso_symmetric by blast


lemma Card_order_iff_ordLeq_card_of:
"Card_order r = (r \<le>o |Field r| )"
proof(auto simp add: Card_order_iff_ordIso_card_of ordIso_iff_ordLeq card_of_Field_ordLess)
  assume "r \<le>o |Field r|" 
  hence "Well_order r" unfolding ordLeq_def by auto 
  thus "|Field r| \<le>o r" using card_of_Field_ordLess by blast
qed


lemma Card_order_iff_Restr_underS:
assumes "Well_order r"
shows "Card_order r = (\<forall>a \<in> Field r. Restr r (underS r a) <o |Field r| )"
using assms unfolding Card_order_iff_ordLeq_card_of 
using ordLeq_iff_ordLess_Restr card_of_Well_order by blast


lemma ordLess_Field:
assumes "r <o r'" 
shows "|Field r| <o r'"
proof-
  have "well_order_on (Field r) r" using assms unfolding ordLess_def 
  by (auto simp add: rel.well_order_on_Well_order)
  hence "|Field r| \<le>o r" using card_of_least by blast
  thus ?thesis using assms ordLeq_ordLess_trans by blast
qed


lemma internalize_card_of_ordLess:
"( |A| <o r) = (\<exists>B < Field r. |A| =o |B| \<and> |B| <o r)"
proof
  assume "|A| <o r"
  then obtain p where 1: "Field p < Field r \<and> |A| =o p \<and> p <o r"
  using internalize_ordLess[of "|A|" r] by blast
  hence "Card_order p" using card_of_Card_order Card_order_ordIso2 by blast
  hence "|Field p| =o p" using card_of_Field_ordIso by blast
  hence "|A| =o |Field p| \<and> |Field p| <o r" 
  using 1 ordIso_equivalence ordIso_ordLess_trans by blast
  thus "\<exists>B < Field r. |A| =o |B| \<and> |B| <o r" using 1 by blast 
next
  assume "\<exists>B < Field r. |A| =o |B| \<and> |B| <o r"
  thus "|A| <o r" using ordIso_ordLess_trans by blast
qed


lemma internalize_card_of_ordLess2:
"( |A| <o |C| ) = (\<exists>B < C. |A| =o |B| \<and> |B| <o |C| )"
using internalize_card_of_ordLess[of "A" "|C|"] Field_card_of[of C] by auto
  

lemma internalize_card_of_ordLeq:
"( |A| \<le>o r) = (\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r)"
proof
  assume "|A| \<le>o r"
  then obtain p where 1: "Field p \<le> Field r \<and> |A| =o p \<and> p \<le>o r"
  using internalize_ordLeq[of "|A|" r] by blast
  hence "Card_order p" using card_of_Card_order Card_order_ordIso2 by blast
  hence "|Field p| =o p" using card_of_Field_ordIso by blast
  hence "|A| =o |Field p| \<and> |Field p| \<le>o r" 
  using 1 ordIso_equivalence ordIso_ordLeq_trans by blast
  thus "\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r" using 1 by blast 
next
  assume "\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r"
  thus "|A| \<le>o r" using ordIso_ordLeq_trans by blast
qed


lemma internalize_card_of_ordLeq2:
"( |A| \<le>o |C| ) = (\<exists>B \<le> C. |A| =o |B| \<and> |B| \<le>o |C| )"
using internalize_card_of_ordLeq[of "A" "|C|"] Field_card_of[of C] by auto


subsection {* Cardinals versus set operations on arbitrary sets *}


text{* Here we embark in a long journey of simple results showing 
that the standard set-theoretic operations are well-behaved w.r.t. the notion of 
cardinal -- essentially, this means that they preserve the ``cardinal identity" 
@{text "=o"} and are monotonic w.r.t. @{text "\<le>o"}.  
*}


lemma subset_ordLeq_strict: 
assumes "A \<le> B" and "|A| <o |B|"
shows "A < B"
proof-
  {assume "\<not>(A < B)"
   hence "A = B" using assms(1) by blast
   hence False using assms(2) not_ordLess_ordIso card_of_refl by blast
  }
  thus ?thesis by blast
qed


corollary subset_ordLeq_diff: 
assumes "A \<le> B" and "|A| <o |B|"
shows "B - A \<noteq> {}"
using assms subset_ordLeq_strict by blast


lemma card_of_empty: "|{}| \<le>o |A|"
using card_of_ordLeq inj_on_id by blast


corollary Card_order_empty:
"Card_order r \<Longrightarrow> |{}| \<le>o r"
using card_of_empty card_of_Field_ordIso ordLeq_ordIso_trans by blast


lemma card_of_image: 
"|f ` A| <=o |A|"
proof(cases "A = {}", simp add: card_of_empty)
  assume "A ~= {}"
  hence "f ` A ~= {}" by auto
  thus "|f ` A| \<le>o |A|"
  using card_of_ordLeq2[of "f ` A" A] by auto
qed


lemma surj_imp_ordLess:
assumes "B <= f ` A"
shows "|B| <=o |A|"
proof-
  have "|B| <=o |f ` A|" using assms card_of_mono1 by auto
  thus ?thesis using card_of_image ordLeq_transitive by blast
qed


lemma Well_order_card_of_empty:
"Well_order r \<Longrightarrow> |{}| \<le>o r"
using card_of_Field_ordLess card_of_empty ordLeq_transitive by blast


lemma card_of_empty2:
assumes LEQ: "|A| =o |{}|"
shows "A = {}"
using assms card_of_ordIso[of A] bij_betw_empty2 by blast


lemma card_of_empty3:
assumes LEQ: "|A| \<le>o |{}|"
shows "A = {}"
using assms by (auto simp add: card_of_empty ordIso_iff_ordLeq card_of_empty2)


lemma card_of_empty4: 
"|{}::'b set| <o |A::'a set| = (A \<noteq> {})"
proof(intro iffI notI)
  assume *: "|{}::'b set| <o |A|" and "A = {}"
  hence "|A| =o |{}::'b set|" 
  using card_of_ordIso unfolding bij_betw_def inj_on_def by blast
  hence "|{}::'b set| =o |A|" using ordIso_symmetric by blast
  with * show False using not_ordLess_ordIso[of "|{}::'b set|" "|A|"] by blast
next
  assume "A \<noteq> {}"
  hence "(\<not> (\<exists>f. inj_on f A \<and> f ` A \<subseteq> {}))" 
  unfolding inj_on_def by blast
  thus "| {} | <o | A |"
  using card_of_ordLess by blast
qed


lemma card_of_empty5: 
"|A| <o |B| \<Longrightarrow> B \<noteq> {}"
using card_of_empty not_ordLess_ordLeq by blast


lemma card_of_empty_ordIso:
"|{}::'a set| =o |{}::'b set|"
using card_of_ordIso unfolding bij_betw_def inj_on_def by blast


lemma card_of_UNIV:
"|A :: 'a set| \<le>o |UNIV :: 'a set|"
using card_of_mono1[of A] by simp


lemma card_of_UNIV2: 
"Card_order r \<Longrightarrow> (r :: 'a rel) \<le>o |UNIV :: 'a set|"
using card_of_UNIV[of "Field r"] card_of_Field_ordIso 
      ordIso_symmetric ordIso_ordLeq_trans by blast


lemma card_of_singl_ordLeq:
assumes "A \<noteq> {}"
shows "|{b}| \<le>o |A|"
proof-
  obtain a where *: "a \<in> A" using assms by auto
  let ?h = "\<lambda> b'::'b. if b' = b then a else undefined"
  have "inj_on ?h {b} \<and> ?h ` {b} \<le> A" 
  using * unfolding inj_on_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed


corollary Card_order_singl_ordLeq:
"\<lbrakk>Card_order r; Field r \<noteq> {}\<rbrakk> \<Longrightarrow> |{b}| \<le>o r"
using card_of_singl_ordLeq[of "Field r" b] 
      card_of_Field_ordIso[of r] ordLeq_ordIso_trans by blast


lemma card_of_Pow: "|A| <o |Pow A|"
using card_of_ordLess2[of "Pow A" A]  Cantors_paradox[of A] 
      Pow_not_empty[of A] by auto


corollary Card_order_Pow: 
"Card_order r \<Longrightarrow> r <o |Pow(Field r)|"
using card_of_Pow card_of_Field_ordIso ordIso_ordLess_trans ordIso_symmetric by blast


corollary card_of_set_type: "|UNIV::'a set| <o |UNIV::'a set set|"
using card_of_Pow[of "UNIV::'a set"] by (auto simp add: Pow_UNIV)


lemma card_of_Pow_mono:
assumes "|A| \<le>o |B|"
shows "|Pow A| \<le>o |Pow B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (image f) (Pow A) \<and> (image f) ` (Pow A) \<le> (Pow B)"
  by (auto simp add: inj_on_image_Pow image_Pow_mono)
  thus ?thesis using card_of_ordLeq[of "Pow A"] by auto
qed


lemma ordIso_Pow_mono:
assumes "r \<le>o r'"
shows "|Pow(Field r)| \<le>o |Pow(Field r')|"
using assms card_of_mono2 card_of_Pow_mono by blast


lemma card_of_Pow_cong:
assumes "|A| =o |B|"
shows "|Pow A| =o |Pow B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (image f) (Pow A) (Pow B)"
  by (auto simp add: bij_betw_image_Pow)
  thus ?thesis using card_of_ordIso[of "Pow A"] by auto
qed


lemma ordIso_Pow_cong:
assumes "r =o r'"
shows "|Pow(Field r)| =o |Pow(Field r')|"
using assms card_of_cong card_of_Pow_cong by blast


lemma card_of_Plus1: "|A| \<le>o |A <+> B|"
proof-
  have "Inl ` A \<le> A <+> B" by auto
  thus ?thesis using inj_Inl[of A] card_of_ordLeq by blast
qed


corollary Card_order_Plus1: 
"Card_order r \<Longrightarrow> r \<le>o |(Field r) <+> B|"
using card_of_Plus1 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Plus2: "|B| \<le>o |A <+> B|"
proof-
  have "Inr ` B \<le> A <+> B" by auto
  thus ?thesis using inj_Inr[of B] card_of_ordLeq by blast
qed


corollary Card_order_Plus2: 
"Card_order r \<Longrightarrow> r \<le>o |A <+> (Field r)|"
using card_of_Plus2 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Plus_empty1: "|A| =o |A <+> {}|"
proof-
  have "bij_betw Inl A (A <+> {})" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed


corollary Card_order_Plus_empty1: 
"Card_order r \<Longrightarrow> r =o |(Field r) <+> {}|"
using card_of_Plus_empty1 card_of_Field_ordIso ordIso_equivalence by blast


lemma card_of_Plus_empty2: "|A| =o |{} <+> A|"
proof-
  have "bij_betw Inr A ({} <+> A)" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed


corollary Card_order_Plus_empty2: 
"Card_order r \<Longrightarrow> r =o |{} <+> (Field r)|"
using card_of_Plus_empty2 card_of_Field_ordIso ordIso_equivalence by blast


lemma card_of_Plus_commute: "|A <+> B| =o |B <+> A|"
proof-
  let ?f = "\<lambda>(c::'a + 'b). case c of Inl a \<Rightarrow> Inr a 
                                   | Inr b \<Rightarrow> Inl b"
  have "bij_betw ?f (A <+> B) (B <+> A)"
  unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Plus_mono1:
assumes "|A| \<le>o |B|"
shows "|A <+> C| \<le>o |B <+> C|"
proof-
  obtain f where 1: "inj_on f A \<and> f ` A \<le> B" 
  using assms card_of_ordLeq[of A] by fastsimp
  obtain g where g_def: 
  "g = (\<lambda>d. case d of Inl a \<Rightarrow> Inl(f a) | Inr (c::'c) \<Rightarrow> Inr c)" by blast
  have "inj_on g (A <+> C) \<and> g ` (A <+> C) \<le> (B <+> C)"
  proof-
    {fix d1 and d2 assume "d1 \<in> A <+> C \<and> d2 \<in> A <+> C" and 
                          "g d1 = g d2"
     hence "d1 = d2" using 1 unfolding inj_on_def 
     by(case_tac d1, case_tac d2, auto simp add: g_def)
    }
    moreover 
    {fix d assume "d \<in> A <+> C"
     hence "g d \<in> B <+> C"  using 1 
     by(case_tac d, auto simp add: g_def)
    }
    ultimately show ?thesis unfolding inj_on_def by auto
  qed
  thus ?thesis using card_of_ordLeq by auto
qed


corollary ordLeq_Plus_mono1: 
assumes "r \<le>o r'" 
shows "|(Field r) <+> C| \<le>o |(Field r') <+> C|"
using assms card_of_mono2 card_of_Plus_mono1 by blast


lemma card_of_Plus_mono2:
assumes "|A| \<le>o |B|"
shows "|C <+> A| \<le>o |C <+> B|"
using assms card_of_Plus_mono1[of A B C] 
      card_of_Plus_commute[of C A]  card_of_Plus_commute[of B C]
      ordIso_ordLeq_trans[of "|C <+> A|"] ordLeq_ordIso_trans[of "|C <+> A|"]
by auto


corollary ordLeq_Plus_mono2: 
assumes "r \<le>o r'" 
shows "|A <+> (Field r)| \<le>o |A <+> (Field r')|"
using assms card_of_mono2 card_of_Plus_mono2 by blast


lemma card_of_Plus_mono:
assumes "|A| \<le>o |B|" and "|C| \<le>o |D|"
shows "|A <+> C| \<le>o |B <+> D|"
using assms card_of_Plus_mono1[of A B C] card_of_Plus_mono2[of C D B]
      ordLeq_transitive[of "|A <+> C|"] by auto


corollary ordLeq_Plus_mono: 
assumes "r \<le>o r'" and "p \<le>o p'"
shows "|(Field r) <+> (Field p)| \<le>o |(Field r') <+> (Field p')|"
using assms card_of_mono2[of r r'] card_of_mono2[of p p'] card_of_Plus_mono by blast


lemma card_of_Plus_cong1:
assumes "|A| =o |B|"
shows "|A <+> C| =o |B <+> C|"
using assms 
by (auto simp add: card_of_Plus_mono1 ordIso_iff_ordLeq)


corollary ordIso_Plus_cong1: 
assumes "r =o r'" 
shows "|(Field r) <+> C| =o |(Field r') <+> C|"
using assms card_of_cong card_of_Plus_cong1 by blast


lemma card_of_Plus_cong2:
assumes "|A| =o |B|"
shows "|C <+> A| =o |C <+> B|"
using assms 
by (auto simp add: card_of_Plus_mono2 ordIso_iff_ordLeq)


corollary ordIso_Plus_cong2: 
assumes "r =o r'" 
shows "|A <+> (Field r)| =o |A <+> (Field r')|"
using assms card_of_cong card_of_Plus_cong2 by blast


lemma card_of_Plus_cong:
assumes "|A| =o |B|" and "|C| =o |D|"
shows "|A <+> C| =o |B <+> D|"
using assms 
by (auto simp add: card_of_Plus_mono ordIso_iff_ordLeq)


corollary ordIso_Plus_cong: 
assumes "r =o r'" and "p =o p'"
shows "|(Field r) <+> (Field p)| =o |(Field r') <+> (Field p')|"
using assms card_of_cong[of r r'] card_of_cong[of p p'] card_of_Plus_cong by blast


lemma card_of_Un1:
shows "|A| \<le>o |A \<union> B| "
using inj_on_id[of A] card_of_ordLeq[of A _] by fastsimp


lemma Card_order_Un1:
shows "Card_order r \<Longrightarrow> |Field r| \<le>o |(Field r) \<union> B| "
using card_of_Un1 card_of_Field_ordIso ordIso_symmetric ordIso_ordLeq_trans by auto


lemma card_of_Un2:
shows "|A| \<le>o |B \<union> A|"
using inj_on_id[of A] card_of_ordLeq[of A _] by fastsimp


lemma Card_order_Un2:
shows "Card_order r \<Longrightarrow> |Field r| \<le>o |A \<union> (Field r)| "
using card_of_Un2 card_of_Field_ordIso ordIso_symmetric ordIso_ordLeq_trans by auto


lemma card_of_diff:
shows "|A - B| \<le>o |A|"
using inj_on_id[of "A - B"] card_of_ordLeq[of "A - B" _] by fastsimp


lemma Un_Plus_bij_betw:
assumes "A Int B = {}"
shows "\<exists>f. bij_betw f (A \<union> B) (A <+> B)"
proof-
  let ?f = "\<lambda> c. if c \<in> A then Inl c else Inr c"
  have "bij_betw ?f (A \<union> B) (A <+> B)"
  using assms by(unfold bij_betw_def inj_on_def, auto)
  thus ?thesis by blast
qed


lemma card_of_Un_Plus_ordIso:
assumes "A Int B = {}"
shows "|A \<union> B| =o |A <+> B|"
using assms card_of_ordIso[of "A \<union> B"] Un_Plus_bij_betw[of A B] by auto


lemma card_of_Un_Plus_ordIso1:
"|A \<union> B| =o |A <+> (B - A)|"
using card_of_Un_Plus_ordIso[of A "B - A"] by auto


lemma card_of_Un_Plus_ordIso2:
"|A \<union> B| =o |(A - B) <+> B|"
using card_of_Un_Plus_ordIso[of "A - B" B] by auto



lemma card_of_Un_Plus_ordLeq:
"|A \<union> B| \<le>o |A <+> B|"
proof-
   let ?f = "\<lambda> c. if c \<in> A then Inl c else Inr c"
   have "inj_on ?f (A \<union> B) \<and> ?f ` (A \<union> B) \<le> A <+> B"
   unfolding inj_on_def by auto
   thus ?thesis using card_of_ordLeq by blast
qed


lemma card_of_Times1: 
assumes "A \<noteq> {}"   
shows "|B| \<le>o |B \<times> A|"
proof -
  from assms obtain x where "x \<in> A" by auto
  hence "inj_on (\<lambda>y. (y, x)) B \<and> (\<lambda>y. (y, x)) ` B \<subseteq> B \<times> A"
    by (blast intro!: inj_onI)
  thus ?thesis using card_of_ordLeq by blast
qed


corollary Card_order_Times1: 
"\<lbrakk>Card_order r; B \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |(Field r) \<times> B|"
using card_of_Times1[of B] card_of_Field_ordIso 
      ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Times_singl1: "|A| =o |A \<times> {b}|"
proof-
  have "bij_betw fst (A \<times> {b}) A" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed


corollary Card_order_Times_singl1: 
"Card_order r \<Longrightarrow> r =o |(Field r) \<times> {b}|"
using card_of_Times_singl1[of _ b] card_of_Field_ordIso ordIso_equivalence by blast


lemma card_of_Times_singl2: "|A| =o |{b} \<times> A|"
proof-
  have "bij_betw snd ({b} \<times> A) A" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed


corollary Card_order_Times_singl2: 
"Card_order r \<Longrightarrow> r =o |{a} \<times> (Field r)|"
using card_of_Times_singl2[of _ a] card_of_Field_ordIso ordIso_equivalence by blast


lemma card_of_Times_commute: "|A \<times> B| =o |B \<times> A|"
proof-
  let ?f = "\<lambda>(a::'a,b::'b). (b,a)"
  have "bij_betw ?f (A \<times> B) (B \<times> A)"
  unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Times2: 
assumes "A \<noteq> {}"   shows "|B| \<le>o |A \<times> B|"
using assms card_of_Times1[of A B] card_of_Times_commute[of B A] 
      ordLeq_ordIso_trans by blast


corollary Card_order_Times2: 
"\<lbrakk>Card_order r; A \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |A \<times> (Field r)|"
using card_of_Times2[of A] card_of_Field_ordIso 
      ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Times3: "|A| \<le>o |A \<times> A|"
using card_of_Times1[of A]
by(cases "A = {}", simp add: card_of_empty, blast)


corollary Card_order_Times3: 
"\<lbrakk>Card_order r\<rbrakk> \<Longrightarrow> |Field r| \<le>o |(Field r) \<times> (Field r)|"
using card_of_Times3 card_of_Field_ordIso 
      ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Plus_Times_bool: "|A <+> A| =o |A \<times> (UNIV::bool set)|"
proof-
  let ?f = "\<lambda>c::'a + 'a. case c of Inl a \<Rightarrow> (a,True) 
                                  |Inr a \<Rightarrow> (a,False)"
  have "bij_betw ?f (A <+> A) (A \<times> (UNIV::bool set))" 
  proof-
    {fix  c1 and c2 assume "?f c1 = ?f c2"
     hence "c1 = c2"
     by(case_tac "c1", case_tac "c2", auto, case_tac "c2", auto)
    }
    moreover 
    {fix c assume "c \<in> A <+> A"
     hence "?f c \<in> A \<times> (UNIV::bool set)" 
     by(case_tac c, auto)
    }
    moreover 
    {fix a bl assume *: "(a,bl) \<in> A \<times> (UNIV::bool set)"
     have "(a,bl) \<in> ?f ` ( A <+> A)"
     proof(cases bl)
       assume bl hence "?f(Inl a) = (a,bl)" by auto
       thus ?thesis using * by force
     next
       assume "\<not> bl" hence "?f(Inr a) = (a,bl)" by auto
       thus ?thesis using * by force
     qed
    }
    ultimately show ?thesis unfolding bij_betw_def inj_on_def by auto
  qed
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Times_mono1:
assumes "|A| \<le>o |B|"
shows "|A \<times> C| \<le>o |B \<times> C|"
proof-
  obtain f where 1: "inj_on f A \<and> f ` A \<le> B" 
  using assms card_of_ordLeq[of A] by fastsimp
  obtain g where g_def: 
  "g = (\<lambda>(a,c::'c). (f a,c))" by blast
  have "inj_on g (A \<times> C) \<and> g ` (A \<times> C) \<le> (B \<times> C)"
  using 1 unfolding inj_on_def using g_def by auto
  thus ?thesis using card_of_ordLeq by auto
qed


corollary ordIso_Times_mono1: 
assumes "r \<le>o r'" 
shows "|(Field r) \<times> C| \<le>o |(Field r') \<times> C|"
using assms card_of_mono2 card_of_Times_mono1 by blast


lemma card_of_Times_mono2:
assumes "|A| \<le>o |B|"
shows "|C \<times> A| \<le>o |C \<times> B|"
using assms card_of_Times_mono1[of A B C] 
      card_of_Times_commute[of C A]  card_of_Times_commute[of B C]
      ordIso_ordLeq_trans[of "|C \<times> A|"] ordLeq_ordIso_trans[of "|C \<times> A|"]
by auto


corollary ordLeq_Times_mono2: 
assumes "r \<le>o r'" 
shows "|A \<times> (Field r)| \<le>o |A \<times> (Field r')|"
using assms card_of_mono2 card_of_Times_mono2 by blast


lemma card_of_Times_mono:
assumes "|A| \<le>o |B|" and "|C| \<le>o |D|"
shows "|A \<times> C| \<le>o |B \<times> D|"
using assms card_of_Times_mono1[of A B C] card_of_Times_mono2[of C D B]
      ordLeq_transitive[of "|A \<times> C|"] by auto


corollary ordLeq_Times_mono: 
assumes "r \<le>o r'" and "p \<le>o p'"
shows "|(Field r) \<times> (Field p)| \<le>o |(Field r') \<times> (Field p')|"
using assms card_of_mono2[of r r'] card_of_mono2[of p p'] card_of_Times_mono by blast


lemma card_of_Times_cong1:
assumes "|A| =o |B|"
shows "|A \<times> C| =o |B \<times> C|"
using assms 
by (auto simp add: card_of_Times_mono1 ordIso_iff_ordLeq)


corollary ordIso_Times_cong1: 
assumes "r =o r'" 
shows "|(Field r) \<times> C| =o |(Field r') \<times> C|"
using assms card_of_cong card_of_Times_cong1 by blast


lemma card_of_Times_cong2:
assumes "|A| =o |B|"
shows "|C \<times> A| =o |C \<times> B|"
using assms 
by (auto simp add: card_of_Times_mono2 ordIso_iff_ordLeq)


corollary ordIso_Times_cong2: 
assumes "r =o r'" 
shows "|A \<times> (Field r)| =o |A \<times> (Field r')|"
using assms card_of_cong card_of_Times_cong2 by blast


lemma card_of_Times_cong:
assumes "|A| =o |B|" and "|C| =o |D|"
shows "|A \<times> C| =o |B \<times> D|"
using assms 
by (auto simp add: card_of_Times_mono ordIso_iff_ordLeq)


corollary ordIso_Times_cong: 
assumes "r =o r'" and "p =o p'"
shows "|(Field r) \<times> (Field p)| =o |(Field r') \<times> (Field p')|"
using assms card_of_cong[of r r'] card_of_cong[of p p'] card_of_Times_cong by blast


lemma card_of_Sigma_mono1:
assumes "\<forall>i \<in> I. |A i| \<le>o |B i|"
shows "|SIGMA i : I. A i| \<le>o |SIGMA i : I. B i|"
proof-
  have "\<forall>i. i \<in> I \<longrightarrow> (\<exists>f. inj_on f (A i) \<and> f ` (A i) \<le> B i)"
  using assms by (auto simp add: card_of_ordLeq) 
  with choice[of "\<lambda> i f. i \<in> I \<longrightarrow> inj_on f (A i) \<and> f ` (A i) \<le> B i"]
  obtain F where 1: "\<forall>i \<in> I. inj_on (F i) (A i) \<and> (F i) ` (A i) \<le> B i" by fastsimp
  obtain g where g_def: "g = (\<lambda>(i,a::'b). (i,F i a))" by blast
  have "inj_on g (Sigma I A) \<and> g ` (Sigma I A) \<le> (Sigma I B)"
  using 1 unfolding inj_on_def using g_def by force 
  thus ?thesis using card_of_ordLeq by auto
qed


lemma card_of_Sigma_mono2:
assumes "inj_on f (I::'i set)" and "f ` I \<le> (J::'j set)"
shows "|SIGMA i : I. (A::'j \<Rightarrow> 'a set) (f i)| \<le>o |SIGMA j : J. A j|"
proof-
  let ?LEFT = "SIGMA i : I. A (f i)" 
  let ?RIGHT = "SIGMA j : J. A j"
  obtain u where u_def: "u = (\<lambda>(i::'i,a::'a). (f i,a))" by blast
  have "inj_on u ?LEFT \<and> u `?LEFT \<le> ?RIGHT"
  using assms unfolding u_def inj_on_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed
 

lemma card_of_Sigma_mono:
assumes INJ: "inj_on f I" and IM: "f ` I \<le> J" and 
        LEQ: "\<forall>j \<in> J. |A j| \<le>o |B j|"
shows "|SIGMA i : I. A (f i)| \<le>o |SIGMA j : J. B j|"
proof-
  have "\<forall>i \<in> I. |A(f i)| \<le>o |B(f i)|" 
  using IM LEQ by blast
  hence "|SIGMA i : I. A (f i)| \<le>o |SIGMA i : I. B (f i)|"
  using card_of_Sigma_mono1 by fastsimp
  moreover have "|SIGMA i : I. B (f i)| \<le>o |SIGMA j : J. B j|"
  using INJ IM card_of_Sigma_mono2 by blast
  ultimately show ?thesis using ordLeq_transitive by blast
qed


lemma ordLeq_Sigma_mono1:
assumes "\<forall>i \<in> I. p i \<le>o r i"
shows "|SIGMA i : I. Field(p i)| \<le>o |SIGMA i : I. Field(r i)|"
using assms by (auto simp add: card_of_mono2 card_of_Sigma_mono1)


lemma ordLeq_Sigma_mono:
assumes "inj_on f I" and "f ` I \<le> J" and 
        "\<forall>j \<in> J. p j \<le>o r j"
shows "|SIGMA i : I. Field(p(f i))| \<le>o |SIGMA j : J. Field(r j)|"
using assms card_of_mono2 card_of_Sigma_mono
      [of f I J "\<lambda> i. Field(p i)" "\<lambda> j. Field(r j)"] by blast


lemma card_of_Sigma_cong1:
assumes "\<forall>i \<in> I. |A i| =o |B i|"
shows "|SIGMA i : I. A i| =o |SIGMA i : I. B i|"
using assms by (auto simp add: card_of_Sigma_mono1 ordIso_iff_ordLeq)


lemma card_of_Sigma_cong2:
assumes "bij_betw f (I::'i set) (J::'j set)"
shows "|SIGMA i : I. (A::'j \<Rightarrow> 'a set) (f i)| =o |SIGMA j : J. A j|"
proof-
  let ?LEFT = "SIGMA i : I. A (f i)" 
  let ?RIGHT = "SIGMA j : J. A j"
  obtain u where u_def: "u = (\<lambda>(i::'i,a::'a). (f i,a))" by blast
  have "bij_betw u ?LEFT ?RIGHT"
  using assms unfolding u_def bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Sigma_cong:
assumes BIJ: "bij_betw f I J" and
        ISO: "\<forall>j \<in> J. |A j| =o |B j|"
shows "|SIGMA i : I. A (f i)| =o |SIGMA j : J. B j|"
proof-
  have "\<forall>i \<in> I. |A(f i)| =o |B(f i)|" 
  using ISO BIJ unfolding bij_betw_def by blast
  hence "|SIGMA i : I. A (f i)| =o |SIGMA i : I. B (f i)|"
  using card_of_Sigma_cong1 by fastsimp
  moreover have "|SIGMA i : I. B (f i)| =o |SIGMA j : J. B j|"
  using BIJ card_of_Sigma_cong2 by blast
  ultimately show ?thesis using ordIso_transitive by blast
qed


lemma ordIso_Sigma_cong1:
assumes "\<forall>i \<in> I. p i =o r i"
shows "|SIGMA i : I. Field(p i)| =o |SIGMA i : I. Field(r i)|"
using assms by (auto simp add: card_of_cong card_of_Sigma_cong1)


lemma ordLeq_Sigma_cong:
assumes "bij_betw f I J" and
        "\<forall>j \<in> J. p j =o r j"
shows "|SIGMA i : I. Field(p(f i))| =o |SIGMA j : J. Field(r j)|"
using assms card_of_cong card_of_Sigma_cong
      [of f I J "\<lambda> j. Field(p j)" "\<lambda> j. Field(r j)"] by blast


corollary card_of_Sigma_Times: 
"\<forall>i \<in> I. |A i| \<le>o |B| \<Longrightarrow> |SIGMA i : I. A i| \<le>o |I \<times> B|" 
using card_of_Sigma_mono1[of I A "\<lambda>i. B"] .


corollary ordLeq_Sigma_Times: 
"\<forall>i \<in> I. p i \<le>o r \<Longrightarrow> |SIGMA i : I. Field (p i)| \<le>o |I \<times> (Field r)|" 
by (auto simp add: card_of_mono2 card_of_Sigma_Times)


lemma card_of_UNION_Sigma:
"|\<Union>i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
using UNION_inj_on_Sigma[of I A] card_of_ordLeq by blast


lemma card_of_bool:
assumes "a1 \<noteq> a2"
shows "|UNIV::bool set| =o |{a1,a2}|"
proof-
  let ?f = "\<lambda> bl. case bl of True \<Rightarrow> a1 | False \<Rightarrow> a2"
  have "bij_betw ?f UNIV {a1,a2}" 
  proof-
    {fix bl1 and bl2 assume "?f  bl1 = ?f bl2"
     hence "bl1 = bl2" using assms by (case_tac bl1, case_tac bl2, auto)
    }
    moreover 
    {fix bl have "?f bl \<in> {a1,a2}" by (case_tac bl, auto)
    }
    moreover 
    {fix a assume *: "a \<in> {a1,a2}"
     have "a \<in> ?f ` UNIV"
     proof(cases "a = a1")
       assume "a = a1"  
       hence "?f True = a" by auto  thus ?thesis by blast
     next
       assume "a \<noteq> a1" hence "a = a2" using * by auto 
       hence "?f False = a" by auto  thus ?thesis by blast
     qed
    }
    ultimately show ?thesis unfolding bij_betw_def inj_on_def by auto
  qed
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Plus_Times_aux:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and  
        LEQ: "|A| \<le>o |B|"
shows "|A <+> B| \<le>o |A \<times> B|"
proof-
  have 1: "|UNIV::bool set| \<le>o |A|" 
  using A2 card_of_mono1[of "{a1,a2}"] card_of_bool[of a1 a2] 
        ordIso_ordLeq_trans[of "|UNIV::bool set|"] by auto
  (*  *)
  have "|A <+> B| \<le>o |B <+> B|" 
  using LEQ card_of_Plus_mono1 by blast
  moreover have "|B <+> B| =o |B \<times> (UNIV::bool set)|"
  using card_of_Plus_Times_bool by blast
  moreover have "|B \<times> (UNIV::bool set)| \<le>o |B \<times> A|"
  using 1 by (auto simp add: card_of_Times_mono2)
  moreover have " |B \<times> A| =o |A \<times> B|" 
  using card_of_Times_commute by blast
  ultimately show "|A <+> B| \<le>o |A \<times> B|" 
  using ordLeq_ordIso_trans[of "|A <+> B|" "|B <+> B|" "|B \<times> (UNIV::bool set)|"] 
        ordLeq_transitive[of "|A <+> B|" "|B \<times> (UNIV::bool set)|" "|B \<times> A|"] 
        ordLeq_ordIso_trans[of "|A <+> B|" "|B \<times> A|" "|A \<times> B|"]
  by auto
qed


lemma card_of_Plus_Times:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and  
        B2: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B" 
shows "|A <+> B| \<le>o |A \<times> B|"
proof-
  {assume "|A| \<le>o |B|" 
   hence ?thesis using assms by (auto simp add: card_of_Plus_Times_aux)
  }
  moreover 
  {assume "|B| \<le>o |A|" 
   hence "|B <+> A| \<le>o |B \<times> A|"
   using assms by (auto simp add: card_of_Plus_Times_aux)
   hence ?thesis 
   using card_of_Plus_commute card_of_Times_commute 
         ordIso_ordLeq_trans ordLeq_ordIso_trans by blast
  }
  ultimately show ?thesis 
  using card_of_Well_order[of A] card_of_Well_order[of B] 
        ordLeq_total[of "|A|"] by blast
qed


corollary Plus_into_Times:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and  
        B2: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B" 
shows "\<exists>f. inj_on f (A <+> B) \<and> f ` (A <+> B) \<le> A \<times> B"
using assms by (auto simp add: card_of_Plus_Times card_of_ordLeq) 


corollary Plus_into_Times_types:
assumes A2: "(a1::'a) \<noteq> a2" and  B2: "(b1::'b) \<noteq> b2" 
shows "\<exists>(f::'a + 'b \<Rightarrow> 'a * 'b). inj f"
using assms Plus_into_Times[of a1 a2 UNIV b1 b2 UNIV] 
by (auto simp add: UNIV_Plus_UNIV)


lemma card_of_ordLeq_finite:
assumes "|A| \<le>o |B|" and "finite B" 
shows "finite A"
using assms unfolding ordLeq_def
using embed_inj_on[of "|A|" "|B|"]  embed_Field[of "|A|" "|B|"] 
      Field_card_of[of "A"] Field_card_of[of "B"] inj_on_finite[of _ "A" "B"] by fastsimp 


lemma card_of_ordIso_finite:
assumes "|A| =o |B|" 
shows "finite A = finite B"
using assms unfolding ordIso_def iso_def_raw
by (auto simp add: Field_card_of bij_betw_finite)


lemma card_of_ordIso_finite_Field:
assumes "Card_order r" and "r =o |A|"
shows "finite(Field r) = finite A"
using assms card_of_Field_ordIso card_of_ordIso_finite ordIso_equivalence by blast


subsection {* Cardinals versus set operations involving infinite sets *}


text{* Here we show that, for infinite sets, most set-theoretic constructions 
do not increase the cardinality.  The cornerstone for this is 
theorem @{text "Card_order_Times_same_infinite"}, which states that self-product 
does not increase cardinality -- the proof of this fact adapts a standard 
set-theoretic argument, as presented, e.g., in the proof of theorem 1.5.11 
at page 47 in \cite{card-book}. Then everything else follows fairly easily.  *}


lemma infinite_iff_card_of_nat:
"infinite A = ( |UNIV::nat set| \<le>o |A| )"
by (auto simp add: infinite_iff_countable_subset card_of_ordLeq)


lemma finite_ordLess_infinite2:
assumes "finite A" and "infinite B"
shows "|A| <o |B|"
using assms 
finite_ordLess_infinite[of "|A|" "|B|"] 
card_of_Well_order[of A] card_of_Well_order[of B]  
Field_card_of[of A] Field_card_of[of B] by auto


text{* The next result corresponds to the ZF fact that all infinite cardinals are 
limit ordinals: *}

lemma Card_order_infinite_not_under:
assumes CARD: "Card_order r" and INF: "infinite (Field r)"
shows "\<not> (\<exists>a. Field r = under r a)"
proof(auto)
  have 0: "Well_order r \<and> wo_rel r \<and> Refl r" 
  using CARD unfolding wo_rel_def card_order_on_def order_on_defs by auto 
  fix a assume *: "Field r = under r a"  
  show False
  proof(cases "a \<in> Field r")
    assume Case1: "a \<notin> Field r"
    hence "under r a = {}" unfolding Field_def rel.under_def by auto
    thus False using INF *  by auto
  next
    let ?r' = "Restr r (underS r a)"
    assume Case2: "a \<in> Field r"
    hence 1: "under r a = underS r a \<union> {a} \<and> a \<notin> underS r a"
    using 0 rel.Refl_under_underS rel.underS_notIn by fastsimp
    have 2: "ofilter r (underS r a) \<and> underS r a < Field r"
    using 0 wo_rel.underS_ofilter * 1 Case2 by auto
    hence "?r' <o r" using 0 using ofilter_ordLess by blast
    moreover 
    have "Field ?r' = underS r a \<and> Well_order ?r'" 
    using  2 0 Field_Restr_ofilter[of r] Well_order_Restr[of r] by blast
    ultimately have "|underS r a| <o r" using ordLess_Field[of ?r'] by auto
    moreover have "|under r a| =o r" using * CARD card_of_Field_ordIso[of r] by auto
    ultimately have "|underS r a| <o |under r a|" 
    using ordIso_symmetric ordLess_ordIso_trans by blast
    moreover 
    {have "\<exists>f. bij_betw f (under r a) (underS r a)"
     using infinite_imp_bij_betw[of "Field r" a] INF * 1 by auto
     hence "|under r a| =o |underS r a|" using card_of_ordIso by blast
    }
    ultimately show False using not_ordLess_ordIso ordIso_symmetric by blast
  qed
qed


theorem Card_order_Times_same_infinite:
assumes CO: "Card_order r" and INF: "infinite(Field r)"
shows "|Field r \<times> Field r| \<le>o r"
proof-
  obtain phi where phi_def: 
  "phi = (\<lambda>r::'a rel. Card_order r \<and> infinite(Field r) \<and> 
                      \<not> |Field r \<times> Field r| \<le>o r )" by blast
  have temp1: "\<forall>r. phi r \<longrightarrow> Well_order r" 
  unfolding phi_def card_order_on_def by auto
  have Ft: "\<not>(\<exists>r. phi r)"
  proof
    assume "\<exists>r. phi r"
    hence "{r. phi r} \<noteq> {} \<and> {r. phi r} \<le> {r. Well_order r}"
    using temp1 by auto
    then obtain r where 1: "phi r" and 2: "\<forall>r'. phi r' \<longrightarrow> r \<le>o r'" and 
                   3: "Card_order r \<and> Well_order r"
    using exists_minim_Well_order[of "{r. phi r}"] temp1 phi_def by blast
    let ?A = "Field r"  let ?r' = "bsqr r"  
    have 4: "Well_order ?r' \<and> Field ?r' = ?A \<times> ?A \<and> |?A| =o r"
    using 3 bsqr_Well_order Field_bsqr card_of_Field_ordIso by blast
    have 5: "Card_order |?A \<times> ?A| \<and> Well_order |?A \<times> ?A|" 
    using card_of_Card_order card_of_Well_order by blast
    (*  *)
    have "r <o |?A \<times> ?A|" 
    using 1 3 5 ordLess_or_ordLeq unfolding phi_def by blast
    moreover have "|?A \<times> ?A| \<le>o ?r'"
    using card_of_least[of "?A \<times> ?A"] 4 by auto
    ultimately have "r <o ?r'" using ordLess_ordLeq_trans by auto
    then obtain f where 6: "embed r ?r' f" and 7: "\<not> bij_betw f ?A (?A \<times> ?A)"
    unfolding ordLess_def embedS_def_raw 
    by (auto simp add: Field_bsqr)
    let ?B = "f ` ?A"
    have "|?A| =o |?B|" 
    using 3 6 embed_inj_on inj_on_imp_bij_betw card_of_ordIso by blast
    hence 8: "r =o |?B|" using 4 ordIso_transitive ordIso_symmetric by blast 
    (*  *)
    have "ofilter ?r' ?B" 
    using 6 embed_Field_ofilter 3 4 by blast
    hence "ofilter ?r' ?B \<and> ?B \<noteq> ?A \<times> ?A \<and> ?B \<noteq> Field ?r'" 
    using 7 unfolding bij_betw_def using 6 3 embed_inj_on 4 by auto
    hence temp2: "ofilter ?r' ?B \<and> ?B < ?A \<times> ?A" 
    using 4 wo_rel_def[of ?r'] wo_rel.ofilter_def[of ?r' ?B] by blast
    have "\<not> (\<exists>a. Field r = under r a)" 
    using 1 unfolding phi_def using Card_order_infinite_not_under[of r] by auto
    then obtain A1 where temp3: "ofilter r A1 \<and> A1 < ?A" and 9: "?B \<le> A1 \<times> A1"  
    using temp2 3 bsqr_ofilter[of r ?B] by blast
    hence "|?B| \<le>o |A1 \<times> A1|" using card_of_mono1 by blast
    hence 10: "r \<le>o |A1 \<times> A1|" using 8 ordIso_ordLeq_trans by blast
    let ?r1 = "Restr r A1"
    have "?r1 <o r" using temp3 ofilter_ordLess 3 by blast
    moreover 
    {have "well_order_on A1 ?r1" using 3 temp3 well_order_on_Restr by blast
     hence "|A1| \<le>o ?r1" using 3 Well_order_Restr card_of_least by blast
    }
    ultimately have 11: "|A1| <o r" using ordLeq_ordLess_trans by blast
    (*  *)
    have "infinite (Field r)" using 1 unfolding phi_def by simp
    hence "infinite ?B" using 8 3 card_of_ordIso_finite_Field[of r ?B] by blast
    hence "infinite A1" using 9 infinite_super finite_cartesian_product by blast
    moreover have temp4: "Field |A1| = A1 \<and> Well_order |A1| \<and> Card_order |A1|" 
    using card_of_Card_order[of A1] card_of_Well_order[of A1]
    by (auto simp add: Field_card_of)
    moreover have "\<not> r \<le>o | A1 |" 
    using temp4 11 3 by (auto simp add: ordLess_iff_not_ordLeq)
    ultimately have "infinite(Field |A1| ) \<and> Card_order |A1| \<and> \<not> r \<le>o | A1 |"
    by (auto simp add: Field_card_of) 
    hence "|Field |A1| \<times> Field |A1| | \<le>o |A1|"
    using 2 unfolding phi_def by auto
    hence "|A1 \<times> A1 | \<le>o |A1|" using temp4 by auto
    hence "r \<le>o |A1|" using 10 ordLeq_transitive by blast
    thus False using 11 not_ordLess_ordLeq by auto
  qed
  thus ?thesis using assms unfolding phi_def by blast
qed


corollary card_of_Times_same_infinite:
assumes "infinite A"
shows "|A \<times> A| =o |A|"
proof-
  let ?r = "|A|"
  have "Field ?r = A \<and> Card_order ?r" 
  using Field_card_of card_of_Card_order[of A] by fastsimp
  hence "|A \<times> A| \<le>o |A|" 
  using Card_order_Times_same_infinite[of ?r] assms by auto
  thus ?thesis using card_of_Times3 ordIso_iff_ordLeq by auto
qed


corollary Times_same_infinite_bij_betw:
assumes "infinite A" 
shows "\<exists>f. bij_betw f (A \<times> A) A"
using assms by (auto simp add: card_of_ordIso card_of_Times_same_infinite) 


corollary Times_same_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)" 
shows "\<exists>(f::('a * 'a) => 'a). bij f"
using assms Times_same_infinite_bij_betw[of "UNIV::'a set"]
by auto


lemma card_of_Times_infinite:
assumes INF: "infinite A" and NE: "B \<noteq> {}" and LEQ: "|B| \<le>o |A|"
shows "|A \<times> B| =o |A| \<and> |B \<times> A| =o |A|"
proof-
  have "|A| \<le>o |A \<times> B| \<and> |A| \<le>o |B \<times> A|" 
  using assms by (auto simp add: card_of_Times1 card_of_Times2)
  moreover 
  {have "|A \<times> B| \<le>o |A \<times> A| \<and> |B \<times> A| \<le>o |A \<times> A|"
   using LEQ card_of_Times_mono1 card_of_Times_mono2 by blast
   moreover have "|A \<times> A| =o |A|" using INF card_of_Times_same_infinite by blast
   ultimately have "|A \<times> B| \<le>o |A| \<and> |B \<times> A| \<le>o |A|"
   using ordLeq_ordIso_trans[of "|A \<times> B|"] ordLeq_ordIso_trans[of "|B \<times> A|"] by auto
  }
  ultimately show ?thesis by (auto simp add: ordIso_iff_ordLeq)
qed 


corollary Card_order_Times_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and 
        NE: "Field p \<noteq> {}" and LEQ: "p \<le>o r"
shows "| (Field r) \<times> (Field p) | =o r \<and> | (Field p) \<times> (Field r) | =o r"
proof- 
  have "|Field r \<times> Field p| =o |Field r| \<and> |Field p \<times> Field r| =o |Field r|"
  using assms by (auto simp add: card_of_Times_infinite card_of_mono2)
  thus ?thesis 
  using assms card_of_Field_ordIso[of r] 
        ordIso_transitive[of "|Field r \<times> Field p|"] 
        ordIso_transitive[of _ "|Field r|"] by blast
qed


corollary Times_infinite_bij_betw:
assumes INF: "infinite A" and NE: "B \<noteq> {}" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A \<times> B) A) \<and> (\<exists>h. bij_betw h (B \<times> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF NE 
  by (auto simp add: card_of_ordIso card_of_Times_infinite) 
qed


corollary Times_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)" and 
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b * 'a) => 'a). bij f) \<and> (\<exists>(h::('a * 'b) => 'a). bij h)"
using assms Times_infinite_bij_betw[of "UNIV::'a set" "UNIV::'b set" g]  
by auto


lemma card_of_Sigma_ordLeq_infinite:
assumes INF: "infinite B" and 
        LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
shows "|SIGMA i : I. A i| \<le>o |B|"
proof(cases "I = {}", simp add: card_of_empty)
  assume *: "I \<noteq> {}"
  have "|SIGMA i : I. A i| \<le>o |I \<times> B|"
  using LEQ card_of_Sigma_Times by blast
  moreover have "|I \<times> B| =o |B|"
  using INF * LEQ_I by (auto simp add: card_of_Times_infinite) 
  ultimately show ?thesis using ordLeq_ordIso_trans by blast
qed


lemma card_of_UNION_ordLeq_infinite:
assumes INF: "infinite B" and 
        LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
shows "|\<Union> i \<in> I. A i| \<le>o |B|"
proof(cases "I = {}", simp add: card_of_empty)
  assume *: "I \<noteq> {}"
  have "|\<Union> i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
  using card_of_UNION_Sigma by blast 
  moreover have "|SIGMA i : I. A i| \<le>o |B|"
  using assms card_of_Sigma_ordLeq_infinite by blast 
  ultimately show ?thesis using ordLeq_transitive by blast
qed 


lemma card_of_Plus_infinite1:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A <+> B| =o |A|"
proof(cases "B = {}", simp add: card_of_Plus_empty1 card_of_Plus_empty2 ordIso_symmetric)
  let ?Inl = "Inl::'a \<Rightarrow> 'a + 'b"  let ?Inr = "Inr::'b \<Rightarrow> 'a + 'b"
  assume *: "B \<noteq> {}"
  then obtain b1 where 1: "b1 \<in> B" by blast
  show ?thesis 
  proof(cases "B = {b1}")
    assume Case1: "B = {b1}"
    have 2: "bij_betw ?Inl A ((?Inl ` A))" 
    unfolding bij_betw_def inj_on_def by auto
    hence 3: "infinite (?Inl ` A)" 
    using INF bij_betw_finite[of ?Inl A] by blast 
    let ?A' = "?Inl ` A \<union> {?Inr b1}"
    obtain g where "bij_betw g (?Inl ` A) ?A'" 
    using 3 infinite_imp_bij_betw2[of "?Inl ` A"] by auto
    moreover have "?A' = A <+> B" using Case1 by blast
    ultimately have "bij_betw g (?Inl ` A) (A <+> B)" by simp
    hence "bij_betw (g o ?Inl) A (A <+> B)" 
    using 2 by (auto simp add: bij_betw_comp)
    thus ?thesis using card_of_ordIso ordIso_symmetric by blast
  next
    assume Case2: "B \<noteq> {b1}"
    with * 1 obtain b2 where 3: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B" by fastsimp
    obtain f where "inj_on f B \<and> f ` B \<le> A" 
    using LEQ card_of_ordLeq[of B] by fastsimp
    with 3 have "f b1 \<noteq> f b2 \<and> {f b1, f b2} \<le> A" 
    unfolding inj_on_def by auto
    with 3 have "|A <+> B| \<le>o |A \<times> B|" 
    by (auto simp add: card_of_Plus_Times) 
    moreover have "|A \<times> B| =o |A|" 
    using assms * by (auto simp add: card_of_Times_infinite)
    ultimately have "|A <+> B| \<le>o |A|" using ordLeq_ordIso_trans by auto
    thus ?thesis using card_of_Plus1 ordIso_iff_ordLeq by blast
  qed
qed


lemma card_of_Plus_infinite2:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|B <+> A| =o |A|"
using assms card_of_Plus_commute card_of_Plus_infinite1 
ordIso_equivalence by blast


lemma card_of_Plus_infinite:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A <+> B| =o |A| \<and> |B <+> A| =o |A|"
using assms by (auto simp add: card_of_Plus_infinite1 card_of_Plus_infinite2)


corollary Card_order_Plus_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and 
        LEQ: "p \<le>o r"
shows "| (Field r) <+> (Field p) | =o r \<and> | (Field p) <+> (Field r) | =o r"
proof- 
  have "| Field r <+> Field p | =o | Field r | \<and>
        | Field p <+> Field r | =o | Field r |"
  using assms by (auto simp add: card_of_Plus_infinite card_of_mono2)
  thus ?thesis 
  using assms card_of_Field_ordIso[of r] 
        ordIso_transitive[of "|Field r <+> Field p|"]
        ordIso_transitive[of _ "|Field r|"] by blast
qed

corollary Plus_infinite_bij_betw:
assumes INF: "infinite A" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A <+> B) A) \<and> (\<exists>h. bij_betw h (B <+> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF 
  by (auto simp add: card_of_ordIso card_of_Plus_infinite) 
qed


corollary Plus_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)" and 
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b + 'a) => 'a). bij f) \<and> (\<exists>(h::('a + 'b) => 'a). bij h)"
using assms Plus_infinite_bij_betw[of "UNIV::'a set" g "UNIV::'b set"]  
by auto


lemma card_of_Un_infinite:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A \<union> B| =o |A| \<and> |B \<union> A| =o |A|"
proof-
  have "|A \<union> B| \<le>o |A <+> B|" 
  by (auto simp add: card_of_Un_Plus_ordLeq) 
  moreover have "|A <+> B| =o |A|" 
  using assms by (auto simp add: card_of_Plus_infinite1)
  ultimately have "|A \<union> B| \<le>o |A|" using ordLeq_ordIso_trans by auto
  hence "|A \<union> B| =o |A|" using card_of_Un1 ordIso_iff_ordLeq by blast
  thus ?thesis using Un_commute[of B A] by auto
qed


corollary Card_order_Un_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and 
        LEQ: "p \<le>o r"
shows "| (Field r) \<union> (Field p) | =o r \<and> | (Field p) \<union> (Field r) | =o r"
proof- 
  have "| Field r \<union> Field p | =o | Field r | \<and>
        | Field p \<union> Field r | =o | Field r |"
  using assms by (auto simp add: card_of_Un_infinite card_of_mono2)
  thus ?thesis 
  using assms card_of_Field_ordIso[of r] 
        ordIso_transitive[of "|Field r \<union> Field p|"]
        ordIso_transitive[of _ "|Field r|"] by blast
qed


lemma card_of_Un_diff_infinite:
assumes INF: "infinite A" and LESS: "|B| <o |A|"
shows "|A - B| =o |A|"
proof-
  obtain C where C_def: "C = A - B" by blast
  have "|A \<union> B| =o |A|" 
  using assms ordLeq_iff_ordLess_or_ordIso card_of_Un_infinite by blast
  moreover have "C \<union> B = A \<union> B" unfolding C_def by auto
  ultimately have 1: "|C \<union> B| =o |A|" by auto
  (*  *)
  {assume *: "|C| \<le>o |B|" 
   moreover 
   {assume **: "finite B" 
    hence "finite C" 
    using card_of_ordLeq_finite * by blast
    hence False using ** INF card_of_ordIso_finite 1 by blast
   }
   hence "infinite B" by auto 
   ultimately have False 
   using  card_of_Un_infinite 1 ordIso_equivalence
          LESS not_ordLess_ordIso by blast
  }
  hence 2: "|B| \<le>o |C|" using card_of_Well_order ordLeq_total by blast
  {assume *: "finite C" 
    hence "finite B" using card_of_ordLeq_finite 2 by blast
    hence False using * INF card_of_ordIso_finite 1 by blast
  }
  hence "infinite C" by auto
  hence "|C| =o |A|"
  using  card_of_Un_infinite 1 2 ordIso_equivalence by blast
  thus ?thesis unfolding C_def .
qed


corollary subset_ordLeq_diff_infinite: 
assumes INF: "infinite B" and SUB: "A \<le> B" and LESS: "|A| <o |B|"
shows "infinite (B - A)"
using assms card_of_Un_diff_infinite card_of_ordIso_finite by blast


lemma card_of_Times_ordLess_infinite:  
assumes INF: "infinite C" and 
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A \<times> B| <o |C|"
proof(cases "A = {} \<or> B = {}")
  assume Case1: "A = {} \<or> B = {}" 
  hence "A \<times> B = {}" by blast
  moreover have "C \<noteq> {}" using  
  LESS1 card_of_empty5 by blast 
  ultimately show ?thesis by(auto simp add:  card_of_empty4)
next
  assume Case2: "\<not>(A = {} \<or> B = {})"
  {assume *: "|C| \<le>o |A \<times> B|"
   hence "infinite (A \<times> B)" using INF card_of_ordLeq_finite by blast
   hence 1: "infinite A \<or> infinite B" using finite_cartesian_product by blast
   {assume Case21: "|A| \<le>o |B|"
    hence "infinite B" using 1 card_of_ordLeq_finite by blast
    hence "|A \<times> B| =o |B|" using Case2 Case21 
    by (auto simp add: card_of_Times_infinite)
    hence False using LESS2 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   moreover 
   {assume Case22: "|B| \<le>o |A|"
    hence "infinite A" using 1 card_of_ordLeq_finite by blast
    hence "|A \<times> B| =o |A|" using Case2 Case22 
    by (auto simp add: card_of_Times_infinite)
    hence False using LESS1 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   ultimately have False using ordLeq_total card_of_Well_order[of A] 
   card_of_Well_order[of B] by blast
  }
  thus ?thesis using ordLess_or_ordLeq[of "|A \<times> B|" "|C|"] 
  card_of_Well_order[of "A \<times> B"] card_of_Well_order[of "C"] by auto
qed


lemma card_of_Plus_ordLess_infinite:  
assumes INF: "infinite C" and 
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A <+> B| <o |C|"
proof(cases "A = {} \<or> B = {}")
  assume Case1: "A = {} \<or> B = {}" 
  hence "|A| =o |A <+> B| \<or> |B| =o |A <+> B|" 
  using card_of_Plus_empty1 card_of_Plus_empty2 by blast
  hence "|A <+> B| =o |A| \<or> |A <+> B| =o |B|"
  using ordIso_symmetric[of "|A|"] ordIso_symmetric[of "|B|"] by blast
  thus ?thesis using LESS1 LESS2 
       ordIso_ordLess_trans[of "|A <+> B|" "|A|"] 
       ordIso_ordLess_trans[of "|A <+> B|" "|B|"] by blast 
next
  assume Case2: "\<not>(A = {} \<or> B = {})"
  {assume *: "|C| \<le>o |A <+> B|"
   hence "infinite (A <+> B)" using INF card_of_ordLeq_finite by blast
   hence 1: "infinite A \<or> infinite B" using finite_Plus by blast
   {assume Case21: "|A| \<le>o |B|"
    hence "infinite B" using 1 card_of_ordLeq_finite by blast
    hence "|A <+> B| =o |B|" using Case2 Case21 
    by (auto simp add: card_of_Plus_infinite)
    hence False using LESS2 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   moreover 
   {assume Case22: "|B| \<le>o |A|"
    hence "infinite A" using 1 card_of_ordLeq_finite by blast
    hence "|A <+> B| =o |A|" using Case2 Case22 
    by (auto simp add: card_of_Plus_infinite)
    hence False using LESS1 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   ultimately have False using ordLeq_total card_of_Well_order[of A] 
   card_of_Well_order[of B] by blast
  }
  thus ?thesis using ordLess_or_ordLeq[of "|A <+> B|" "|C|"] 
  card_of_Well_order[of "A <+> B"] card_of_Well_order[of "C"] by auto
qed


lemma card_of_Un_ordLess_infinite:  
assumes INF: "infinite C" and 
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A \<union> B| <o |C|"
using assms card_of_Plus_ordLess_infinite card_of_Un_Plus_ordLeq 
      ordLeq_ordLess_trans by blast


lemma card_of_Un_singl_ordLess_infinite1:
assumes "infinite B" and "|A| <o |B|" 
shows "|{a} Un A| <o |B|"
proof-
  have "|{a}| <o |B|" using assms by(auto simp add: finite_ordLess_infinite2) 
  thus ?thesis using assms card_of_Un_ordLess_infinite[of B] by fastsimp
qed


lemma card_of_Un_singl_ordLess_infinite:
assumes "infinite B"  
shows "( |A| <o |B| ) = ( |{a} Un A| <o |B| )"
using assms card_of_Un_singl_ordLess_infinite1[of B A] 
proof(auto)
  assume "|insert a A| <o |B|"
  moreover have "|A| <=o |insert a A|" using card_of_mono1[of A] by auto
  ultimately show "|A| <o |B|" using ordLeq_ordLess_trans by blast
qed


subsection {* Cardinals versus lists  *}


definition List :: "'a set \<Rightarrow> 'a list set"
where "List A \<equiv> {l. set l \<le> A}" 


text{* The next is an auxiliary operator, which shall be used for inductive 
proofs of facts concerning the cardinality of @{text "List"} : *}

definition nList :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
where "nList A n \<equiv> {l. set l \<le> A \<and> length l = n}"


lemma List_UNIV: "List UNIV = UNIV"
unfolding List_def by auto


lemma List_UNION_nList: "List A = (\<Union> n. nList A n)"
unfolding List_def nList_def by blast


lemma List_mono: "A \<le> B \<Longrightarrow> List A \<le> List B"
unfolding List_def by auto


lemma card_of_List: "|A| \<le>o |List A|"
proof-
  let ?h = "\<lambda> a. [a]"
  have "inj_on ?h A \<and> ?h ` A \<le> List A" 
  unfolding inj_on_def List_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed


lemma Cad_order_List: "Card_order r \<Longrightarrow> r \<le>o |List(Field r) |"
using card_of_List card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma Union_set_List:
"Union(set ` (List A)) = A"
unfolding List_def proof(auto)
  fix a assume "a \<in> A"
  hence "set [a] \<le> A \<and> a \<in> set [a]" by auto
  thus "\<exists>l. set l \<le> A \<and> a \<in> set l" by blast
qed


lemma inj_on_map_List: 
assumes "inj_on f A"
shows "inj_on (map f) (List A)"
using assms Union_set_List[of A] inj_on_mapI[of f "List A"] by auto


lemma map_List_mono:
assumes "f ` A \<le> B"
shows "(map f) ` (List A) \<le> List B"
using assms unfolding List_def by (auto, blast) (* lethal combination of methods :)  *)


lemma map_List_surjective:
assumes "f ` A = B"
shows "(map f) ` (List A) = List B"
using assms unfolding List_def 
proof (auto, blast)
  fix l' assume *: "set l' \<le> f ` A"
  have "set l' \<le> f ` A \<longrightarrow> l' \<in> map f ` {l. set l \<le> A}"
  proof(induct l', auto)
    fix l a 
    assume "a \<in> A" and "set l \<le> A" and 
           IH: "f ` (set l) \<le> f ` A"
    hence "set (a # l) \<le> A" by auto
    hence "map f (a # l) \<in> map f ` {l. set l \<le> A}" by blast
    thus "f a # map f l \<in> map f ` {l. set l \<le> A}" by auto
  qed
  thus "l' \<in> map f ` {l. set l \<le> A}" using * by auto
qed


lemma bij_betw_map_List: 
assumes "bij_betw f A B"
shows "bij_betw (map f) (List A) (List B)"
using assms unfolding bij_betw_def using inj_on_map_List map_List_surjective by blast


lemma card_of_List_mono:
assumes "|A| \<le>o |B|"
shows "|List A| \<le>o |List B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (map f) (List A) \<and> (map f) ` (List A) \<le> (List B)"
  by (auto simp add: inj_on_map_List map_List_mono)
  thus ?thesis using card_of_ordLeq[of "List A"] by auto
qed


lemma ordIso_List_mono:
assumes "r \<le>o r'"
shows "|List(Field r)| \<le>o |List(Field r')|"
using assms card_of_mono2 card_of_List_mono by blast


lemma card_of_List_cong:
assumes "|A| =o |B|"
shows "|List A| =o |List B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (map f) (List A) (List B)"
  by (auto simp add: bij_betw_map_List)
  thus ?thesis using card_of_ordIso[of "List A"] by auto
qed


lemma ordIso_List_cong:
assumes "r =o r'"
shows "|List(Field r)| =o |List(Field r')|"
using assms card_of_cong card_of_List_cong by blast


lemma length_Suc: "(\<exists>n. length l = Suc n) = (\<exists>a l'. l = a # l')"
by(induct l, auto)


lemma nList_0: "nList A 0 = {[]}"
unfolding nList_def by auto


lemma nList_not_empty: 
assumes "A \<noteq> {}" 
shows "nList A n \<noteq> {}"
proof(induct n, simp add: nList_0)
  fix n assume "nList A n \<noteq> {}"
  then obtain a and l where "a \<in> A \<and> l \<in> nList A n" using assms by auto
  hence "a # l \<in> nList A (Suc n)" unfolding nList_def by auto
  thus "nList A (Suc n) \<noteq> {}" by auto
qed


lemma Nil_in_List: "[] \<in> List A"
unfolding List_def by auto


lemma List_not_empty: "List A \<noteq> {}"
using Nil_in_List by blast


lemma card_of_nList_Succ: "|nList A (Suc n)| =o |A \<times> (nList A n)|"
proof-
  let ?B = "A \<times> (nList A n)"   let ?h = "\<lambda>(a,l). a # l"
  have "inj_on ?h ?B \<and> ?h ` ?B \<le> nList A (Suc n)" 
  unfolding inj_on_def nList_def by auto
  moreover have "nList A (Suc n) \<le> ?h ` ?B"
  proof(auto)
    fix l assume "l \<in> nList A (Suc n)"
    hence 1: "length l = Suc n \<and> set l \<le> A" unfolding nList_def by auto 
    then obtain a and l' where 2: "l = a # l'" using length_Suc[of l] by auto
    hence "a \<in> A \<and> set l' \<le> A \<and> length l' = n" using 1 by auto
    thus "l \<in> ?h ` ?B"  using 2 unfolding nList_def by auto
  qed
  ultimately have "bij_betw ?h ?B (nList A (Suc n))"
  unfolding bij_betw_def by auto
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed


lemma card_of_nList_infinite:
assumes "infinite A"
shows "|nList A n| \<le>o |A|"
proof(induct n)
  show "|nList A 0| \<le>o |A|" 
  using assms nList_0[of A] card_of_singl_ordLeq[of A] by fastsimp
next
  fix n assume IH: "|nList A n| \<le>o |A|"
  have "|nList A (Suc n)| =o |A \<times> (nList A n)|" 
  using card_of_nList_Succ by blast
  moreover 
  {have "nList A n \<noteq> {}" using assms nList_not_empty[of A] by blast
   hence "|A \<times> (nList A n)| =o |A|" 
   using assms IH by (auto simp add: card_of_Times_infinite)
  }
  ultimately show "|nList A (Suc n)| \<le>o |A|"
  using ordIso_transitive ordIso_iff_ordLeq by blast
qed


lemma card_of_List_infinite:
assumes "infinite A"
shows "|List A| =o |A|"
proof-
  have "|List A| \<le>o |A|" 
  using assms
  by (auto simp add: List_UNION_nList card_of_UNION_ordLeq_infinite
                     infinite_iff_card_of_nat card_of_nList_infinite)
  thus ?thesis using card_of_List ordIso_iff_ordLeq by blast
qed


lemma Card_order_List_infinite:
assumes "Card_order r" and "infinite(Field r)"
shows "|List(Field r)| =o r"
using assms card_of_List_infinite card_of_Field_ordIso ordIso_transitive by blast


corollary List_infinite_bij_betw:
assumes "infinite A"
shows "\<exists>f. bij_betw f (List A) A"
using assms card_of_List_infinite card_of_ordIso by blast


corollary List_infinite_bij_betw_types:
assumes "infinite(UNIV :: 'a set)"
shows "\<exists>(f::'a list \<Rightarrow> 'a). bij f"
using assms assms List_infinite_bij_betw[of "UNIV::'a set"]
by (auto simp add: List_UNIV)



subsection {* Cardinals versus the set-of-finite-sets operator  *}


definition Fpow :: "'a set \<Rightarrow> 'a set set"
where "Fpow A \<equiv> {X. X \<le> A \<and> finite X}"


lemma Fpow_mono: "A \<le> B \<Longrightarrow> Fpow A \<le> Fpow B"
unfolding Fpow_def by auto


lemma empty_in_Fpow: "{} \<in> Fpow A"
unfolding Fpow_def by auto


lemma Fpow_not_empty: "Fpow A \<noteq> {}"
using empty_in_Fpow by blast


lemma Fpow_subset_Pow: "Fpow A \<le> Pow A"
unfolding Fpow_def by auto


lemma card_of_Fpow: "|A| \<le>o |Fpow A|"
proof-
  let ?h = "\<lambda> a. {a}"
  have "inj_on ?h A \<and> ?h ` A \<le> Fpow A" 
  unfolding inj_on_def Fpow_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed


lemma Card_order_Fpow: "Card_order r \<Longrightarrow> r \<le>o |Fpow(Field r) |"
using card_of_Fpow card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma Fpow_Pow_finite: "Fpow A = Pow A Int {A. finite A}"
unfolding Fpow_def Pow_def by blast     


lemma inj_on_image_Fpow: 
assumes "inj_on f A"
shows "inj_on (image f) (Fpow A)"
using assms Fpow_subset_Pow[of A] subset_inj_on[of "image f" "Pow A"] 
      inj_on_image_Pow by blast


lemma image_Fpow_mono:
assumes "f ` A \<le> B"
shows "(image f) ` (Fpow A) \<le> Fpow B"
using assms by(unfold Fpow_def, auto)
 

lemma image_Fpow_surjective:
assumes "f ` A = B"
shows "(image f) ` (Fpow A) = Fpow B"
using assms proof(unfold Fpow_def, auto)
  fix Y assume *: "Y \<le> f ` A" and **: "finite Y"
  hence "\<forall>b \<in> Y. \<exists>a. a \<in> A \<and> f a = b" by auto 
  with bchoice[of Y "\<lambda>b a. a \<in> A \<and> f a = b"]
  obtain g where 1: "\<forall>b \<in> Y. g b \<in> A \<and> f(g b) = b" by blast 
  obtain X where X_def: "X = g ` Y" by blast 
  have "f ` X = Y \<and> X \<le> A \<and> finite X"
  by(unfold X_def, force simp add: ** 1) 
  thus "Y \<in> (image f) ` {X. X \<le> A \<and> finite X}" by auto
qed


lemma bij_betw_image_Fpow: 
assumes "bij_betw f A B"
shows "bij_betw (image f) (Fpow A) (Fpow B)"
using assms unfolding bij_betw_def 
by (auto simp add: inj_on_image_Fpow image_Fpow_surjective)


lemma card_of_Fpow_mono:
assumes "|A| \<le>o |B|"
shows "|Fpow A| \<le>o |Fpow B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (image f) (Fpow A) \<and> (image f) ` (Fpow A) \<le> (Fpow B)"
  by (auto simp add: inj_on_image_Fpow image_Fpow_mono)
  thus ?thesis using card_of_ordLeq[of "Fpow A"] by auto
qed


lemma ordIso_Fpow_mono:
assumes "r \<le>o r'"
shows "|Fpow(Field r)| \<le>o |Fpow(Field r')|"
using assms card_of_mono2 card_of_Fpow_mono by blast


lemma card_of_Fpow_cong:
assumes "|A| =o |B|"
shows "|Fpow A| =o |Fpow B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (image f) (Fpow A) (Fpow B)"
  by (auto simp add: bij_betw_image_Fpow)
  thus ?thesis using card_of_ordIso[of "Fpow A"] by auto
qed


lemma ordIso_Fpow_cong:
assumes "r =o r'"
shows "|Fpow(Field r)| =o |Fpow(Field r')|"
using assms card_of_cong card_of_Fpow_cong by blast


lemma card_of_Fpow_List: "|Fpow A| \<le>o |List A|"
proof-
  have "set ` (List A) = Fpow A"
  unfolding List_def Fpow_def using finite_list finite_set by blast
  thus ?thesis using card_of_ordLeq2[of "Fpow A"] Fpow_not_empty[of A] by auto
qed


lemma card_of_Fpow_infinite: 
assumes "infinite A"
shows "|Fpow A| =o |A|"
using assms card_of_Fpow_List card_of_List_infinite card_of_Fpow 
      ordLeq_ordIso_trans ordIso_iff_ordLeq by blast


corollary Fpow_infinite_bij_betw:
assumes "infinite A"
shows "\<exists>f. bij_betw f (Fpow A) A"
using assms card_of_Fpow_infinite card_of_ordIso by blast



subsection {* The cardinal $\omega$ and the finite cardinals  *}


text{* The cardinal $\omega$, of natural numbers, shall be the standard non-strict 
order relation on 
@{text "nat"}, that we abbreviate by @{text "natLeq"}.  The finite cardinals 
shall be the restrictions of these relations to the numbers smaller than 
fixed numbers @{text "n"}, that we abbreviate by @{text "natLeq_on n"}.  *}

abbreviation "(natLeq::nat * nat \<Rightarrow> bool) \<equiv> {(x,y). x \<le> y}"
abbreviation "(natLess::nat * nat \<Rightarrow> bool) \<equiv> {(x,y). x < y}"

abbreviation natLeq_on :: "nat \<Rightarrow> (nat * nat \<Rightarrow> bool)"
where "natLeq_on n \<equiv> {(x,y). x < n \<and> y < n \<and> x \<le> y}"


subsubsection {* First as well-orders *}


lemma Field_natLeq: "Field natLeq = (UNIV::nat set)"
by(unfold Field_def, auto)


lemma Field_natLess: "Field natLess = (UNIV::nat set)"
by(unfold Field_def, auto)
  

lemma natLeq_Refl: "Refl natLeq"
unfolding refl_on_def Field_def by auto


lemma natLeq_trans: "trans natLeq"
unfolding trans_def by auto


lemma natLeq_Preorder: "Preorder natLeq"
unfolding preorder_on_def 
by (auto simp add: natLeq_Refl natLeq_trans)


lemma natLeq_antisym: "antisym natLeq"
unfolding antisym_def by auto


lemma natLeq_Partial_order: "Partial_order natLeq"
unfolding partial_order_on_def 
by (auto simp add: natLeq_Preorder natLeq_antisym)


lemma natLeq_Total: "Total natLeq"
unfolding total_on_def by auto


lemma natLeq_Linear_order: "Linear_order natLeq"
unfolding linear_order_on_def 
by (auto simp add: natLeq_Partial_order natLeq_Total)


lemma natLeq_natLess_Id: "natLess = natLeq - Id"
by auto


lemma natLeq_Well_order: "Well_order natLeq"
unfolding well_order_on_def 
using natLeq_Linear_order wf_less natLeq_natLess_Id by auto


corollary natLeq_well_order_on: "well_order_on UNIV natLeq"
using natLeq_Well_order Field_natLeq by auto


lemma natLeq_wo_rel: "wo_rel natLeq"
unfolding wo_rel_def using natLeq_Well_order .


lemma natLeq_ofilter_less: "ofilter natLeq {0 ..< n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def, 
   simp add:  Field_natLeq, unfold rel.under_def, auto)


lemma natLeq_ofilter_leq: "ofilter natLeq {0 .. n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def, 
   simp add:  Field_natLeq, unfold rel.under_def, auto)


lemma natLeq_UNIV_ofilter: "ofilter natLeq UNIV"
using natLeq_wo_rel Field_natLeq wo_rel.Field_ofilter[of natLeq] by auto


lemma closed_nat_set_iff:
assumes "\<forall>(m::nat) n. n \<in> A \<and> m \<le> n \<longrightarrow> m \<in> A"
shows "A = UNIV \<or> (\<exists>n. A = {0 ..< n})"
proof-
  {assume "A \<noteq> UNIV" hence "\<exists>n. n \<notin> A" by blast
   moreover obtain n where n_def: "n = (LEAST n. n \<notin> A)" by blast
   ultimately have 1: "n \<notin> A \<and> (\<forall>m. m < n \<longrightarrow> m \<in> A)" 
   using LeastI_ex[of "\<lambda> n. n \<notin> A"] n_def Least_le[of "\<lambda> n. n \<notin> A"] by fastsimp
   have "A = {0 ..< n}"
   proof(auto simp add: 1)
     fix m assume *: "m \<in> A"
     {assume "n \<le> m" with assms * have "n \<in> A" by blast
      hence False using 1 by auto
     }
     thus "m < n" by fastsimp
   qed
   hence "\<exists>n. A = {0 ..< n}" by blast
  } 
  thus ?thesis by blast
qed


lemma natLeq_ofilter_iff:
"ofilter natLeq A = (A = UNIV \<or> (\<exists>n. A = {0 ..< n}))"
proof(rule iffI)
  assume "ofilter natLeq A"
  hence "\<forall>m n. n \<in> A \<and> m \<le> n \<longrightarrow> m \<in> A"
  by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def rel.under_def)
  thus "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
next 
  assume "A = UNIV \<or> (\<exists>n. A = {0 ..< n})"
  thus "ofilter natLeq A"
  by(auto simp add: natLeq_ofilter_less natLeq_UNIV_ofilter)
qed


lemma Field_natLeq_on: "Field (natLeq_on n) = {0 ..< n}"
unfolding Field_def by auto


lemma natLeq_underS_less: "underS natLeq n = {0 ..< n}"
unfolding rel.underS_def by auto


lemma natLeq_under_leq: "under natLeq n = {0 .. n}"
unfolding rel.under_def by auto


lemma Restr_natLeq: "Restr natLeq {0 ..< n} = natLeq_on n"
by auto


lemma Restr_natLeq2: 
"Restr natLeq (underS natLeq n) = natLeq_on n"
by (auto simp add: Restr_natLeq natLeq_underS_less)


lemma natLeq_on_Well_order: "Well_order(natLeq_on n)"
using Restr_natLeq[of n] natLeq_Well_order 
      Well_order_Restr[of natLeq "{0..<n}"] by auto


corollary natLeq_on_well_order_on: "well_order_on {0 ..< n} (natLeq_on n)"
using natLeq_on_Well_order Field_natLeq_on by auto


lemma natLeq_on_wo_rel: "wo_rel(natLeq_on n)"
unfolding wo_rel_def using natLeq_on_Well_order .


lemma natLeq_on_ofilter_less_eq: 
"n \<le> m \<Longrightarrow> ofilter(natLeq_on m) {0 ..< n}"
by(auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def, 
   simp add:  Field_natLeq_on, unfold rel.under_def, auto)


corollary natLeq_on_ofilter: 
"ofilter(natLeq_on n) {0 ..< n}"
by (auto simp add: natLeq_on_ofilter_less_eq)


lemma natLeq_on_ofilter_less: 
"n < m \<Longrightarrow> ofilter (natLeq_on m) {0 .. n}"
by(auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def, 
   simp add: Field_natLeq_on, unfold rel.under_def, auto)


lemma natLeq_on_ordLess_natLeq: "natLeq_on n <o natLeq"
using Field_natLeq Field_natLeq_on[of n] nat_infinite 
      finite_ordLess_infinite[of "natLeq_on n" natLeq]
      natLeq_Well_order natLeq_on_Well_order[of n] by auto


lemma natLeq_on_injective: 
"natLeq_on m = natLeq_on n \<Longrightarrow> m = n" 
using Field_natLeq_on[of m] Field_natLeq_on[of n] 
      atLeastLessThan_injective[of m n] by auto


lemma natLeq_on_injective_ordIso: 
"(natLeq_on m =o natLeq_on n) = (m = n)"
proof(auto simp add: natLeq_on_Well_order ordIso_reflexive)
  assume "natLeq_on m =o natLeq_on n"
  then obtain f where "bij_betw f {0..<m} {0..<n}" 
  using Field_natLeq_on assms unfolding ordIso_def iso_def_raw by auto
  thus "m = n" using atLeastLessThan_injective2 by blast 
qed


lemma natLeq_on_ofilter_iff:
"ofilter (natLeq_on m) A = (\<exists>n \<le> m. A = {0 ..< n})"
proof(rule iffI)
  assume *: "ofilter (natLeq_on m) A"
  hence 1: "A \<le> {0..<m}" 
  by (auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def rel.under_def Field_natLeq_on)
  hence "\<forall>n1 n2. n2 \<in> A \<and> n1 \<le> n2 \<longrightarrow> n1 \<in> A"
  using * by(fastsimp simp add: natLeq_on_wo_rel wo_rel.ofilter_def rel.under_def)
  hence "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
  thus "\<exists>n \<le> m. A = {0 ..< n}" using 1 atLeastLessThan_less_eq by blast 
next 
  assume "(\<exists>n\<le>m. A = {0 ..< n})"
  thus "ofilter (natLeq_on m) A" by (auto simp add: natLeq_on_ofilter_less_eq)
qed



subsubsection {* Then as cardinals *}


lemma natLeq_Card_order: "Card_order natLeq"
proof(auto simp add: natLeq_Well_order 
      Card_order_iff_Restr_underS Restr_natLeq2, simp add:  Field_natLeq)
  fix n have "finite(Field (natLeq_on n))" 
  unfolding Field_natLeq_on by auto
  moreover have "infinite(UNIV::nat set)" by auto
  ultimately show "natLeq_on n <o |UNIV::nat set|"
  using finite_ordLess_infinite[of "natLeq_on n" "|UNIV::nat set|"] 
        Field_card_of[of "UNIV::nat set"]
        card_of_Well_order[of "UNIV::nat set"] natLeq_on_Well_order[of n] by auto
qed


corollary card_of_Field_natLeq:
"|Field natLeq| =o natLeq"
using Field_natLeq natLeq_Card_order Card_order_iff_ordIso_card_of[of natLeq] 
      ordIso_symmetric[of natLeq] by auto


corollary card_of_nat:
"|UNIV::nat set| =o natLeq"
using Field_natLeq card_of_Field_natLeq by auto


corollary infinite_iff_natLeq_ordLeq:
"infinite A = ( natLeq \<le>o |A| )"
using infinite_iff_card_of_nat[of A] card_of_nat 
      ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast


lemma ordIso_natLeq_infinite1:
"|A| =o natLeq \<Longrightarrow> infinite A" 
using ordIso_symmetric ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast


lemma ordIso_natLeq_infinite2:
"natLeq =o |A| \<Longrightarrow> infinite A" 
using ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast


corollary finite_iff_ordLess_natLeq:
"finite A = ( |A| <o natLeq)"
using infinite_iff_natLeq_ordLeq ordLess_iff_not_ordLeq 
      card_of_Well_order natLeq_Well_order by blast


lemma ordIso_natLeq_on_imp_finite:
"|A| =o natLeq_on n \<Longrightarrow> finite A"
unfolding ordIso_def iso_def_raw 
by (auto simp add: Field_card_of Field_natLeq_on bij_betw_finite)


lemma natLeq_on_Card_order: "Card_order (natLeq_on n)"
proof(unfold card_order_on_def, 
      auto simp add: natLeq_on_Well_order, simp add: Field_natLeq_on)
  fix r assume "well_order_on {0..<n} r"
  thus "natLeq_on n \<le>o r"
  using finite_atLeastLessThan natLeq_on_well_order_on 
        finite_well_order_on_ordIso ordIso_iff_ordLeq by blast
qed


corollary card_of_Field_natLeq_on:
"|Field (natLeq_on n)| =o natLeq_on n"
using Field_natLeq_on natLeq_on_Card_order 
      Card_order_iff_ordIso_card_of[of "natLeq_on n"] 
      ordIso_symmetric[of "natLeq_on n"] by auto


corollary card_of_less:
"|{0 ..< n}| =o natLeq_on n"
using Field_natLeq_on card_of_Field_natLeq_on by auto


lemma ordLeq_natLeq_on_imp_finite:
assumes "|A| \<le>o natLeq_on n" 
shows "finite A"
proof-
  have "|A| \<le>o |{0 ..< n}|" 
  using assms card_of_less ordIso_symmetric ordLeq_ordIso_trans by blast
  thus ?thesis by (auto simp add: card_of_ordLeq_finite)
qed


lemma natLeq_on_ordLeq_less_eq: 
"((natLeq_on m) \<le>o (natLeq_on n)) = (m \<le> n)"
proof
  assume "natLeq_on m \<le>o natLeq_on n"
  then obtain f where "inj_on f {0..<m} \<and> f ` {0..<m} \<le> {0..<n}" 
  using Field_natLeq_on[of m] Field_natLeq_on[of n]
  unfolding ordLeq_def using embed_inj_on[of "natLeq_on m"  "natLeq_on n"] 
  embed_Field[of "natLeq_on m" "natLeq_on n"] using natLeq_on_Well_order[of m] by fastsimp
  thus "m \<le> n" using atLeastLessThan_less_eq2 by blast
next
  assume "m \<le> n"
  hence "inj_on id {0..<m} \<and> id ` {0..<m} \<le> {0..<n}" unfolding inj_on_def by auto
  hence "|{0..<m}| \<le>o |{0..<n}|" using card_of_ordLeq by blast
  thus "natLeq_on m \<le>o natLeq_on n" 
  using card_of_less ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast
qed


lemma natLeq_on_ordLeq_less: 
"((natLeq_on m) <o (natLeq_on n)) = (m < n)"
by (auto simp add: ordLess_iff_not_ordLeq natLeq_on_Well_order natLeq_on_ordLeq_less_eq)
 

subsubsection {* "Backwards compatibility" with the numeric cardinal operator for finite sets *}


lemma finite_card_of_iff_card:
assumes FIN: "finite A" and FIN': "finite B" 
shows "( |A| =o |B| ) = (card A = card B)"
using assms card_of_ordIso[of A B] bij_betw_iff_card[of A B] by blast


lemma finite_card_of_iff_card2:
assumes FIN: "finite A" and FIN': "finite B" 
shows "( |A| \<le>o |B| ) = (card A \<le> card B)"
using assms card_of_ordLeq[of A B] inj_on_iff_card[of A B] by blast


lemma finite_card_of_iff_card3:
assumes FIN: "finite A" and FIN': "finite B" 
shows "( |A| <o |B| ) = (card A < card B)"
using assms 
by (auto simp add: ordLess_iff_not_ordLeq finite_card_of_iff_card2 card_of_Well_order)


lemma finite_imp_card_of_natLeq_on:
assumes "finite A"
shows "|A| =o natLeq_on (card A)"
proof-
  obtain h where "bij_betw h A {0 ..< card A}"
  using assms ex_bij_betw_finite_nat by blast
  thus ?thesis using card_of_ordIso card_of_less ordIso_equivalence by blast
qed


lemma finite_iff_card_of_natLeq_on:
"finite A = (\<exists>n. |A| =o natLeq_on n)"
using finite_imp_card_of_natLeq_on[of A]
by(auto simp add: ordIso_natLeq_on_imp_finite)


lemma card_Field_natLeq_on: 
"card(Field(natLeq_on n)) = n"
using Field_natLeq_on card_atLeastLessThan by auto



subsection {* The successor of a cardinal *}


text{* First we define @{text "isCardSuc r r'"}, the notion of @{text "r'"} 
being a successor cardinal of @{text "r"}. Although the definition does 
not require @{text "r"} to be a cardinal, only this case will be meaningful.  *}


definition isCardSuc :: "'a rel \<Rightarrow> 'a set rel \<Rightarrow> bool"
where 
"isCardSuc r r' \<equiv> 
 Card_order r' \<and> r <o r' \<and> 
 (\<forall>(r''::'a set rel). Card_order r'' \<and> r <o r'' \<longrightarrow> r' \<le>o r'')"


text{* Now we introduce the cardinal-successor operator @{text "cardSuc"}, 
by picking {\em some} cardinal-order relation fulfilling @{text "isCardSuc"}.  
Again, the picked item shall be proved unique up to order-isomorphism. *}


definition cardSuc :: "'a rel \<Rightarrow> 'a set rel"
where 
"cardSuc r \<equiv> SOME r'. isCardSuc r r'"


lemma exists_minim_Card_order:
"\<lbrakk>R \<noteq> {}; \<forall>r \<in> R. Card_order r\<rbrakk> \<Longrightarrow> \<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'"
unfolding card_order_on_def using exists_minim_Well_order by blast


lemma exists_isCardSuc: 
assumes "Card_order r"
shows "\<exists>r'. isCardSuc r r'" 
proof-
  let ?R = "{(r'::'a set rel). Card_order r' \<and> r <o r'}"
  have "|Pow(Field r)| \<in> ?R \<and> (\<forall>r \<in> ?R. Card_order r)" using assms 
  by(auto simp add: card_of_Card_order Card_order_Pow)
  then obtain r where "r \<in> ?R \<and> (\<forall>r' \<in> ?R. r \<le>o r')"
  using exists_minim_Card_order[of ?R] by blast
  thus ?thesis unfolding isCardSuc_def by auto
qed


lemma cardSuc_isCardSuc: 
assumes "Card_order r"
shows "isCardSuc r (cardSuc r)"
unfolding cardSuc_def using assms 
by (auto simp add: exists_isCardSuc someI_ex) 


lemma cardSuc_Card_order:
"Card_order r \<Longrightarrow> Card_order(cardSuc r)"
using cardSuc_isCardSuc unfolding isCardSuc_def by blast


lemma cardSuc_Well_order:
"Card_order r \<Longrightarrow> Well_order(cardSuc r)"
using cardSuc_Card_order unfolding card_order_on_def by blast


lemma cardSuc_greater:
"Card_order r \<Longrightarrow> r <o cardSuc r"
using cardSuc_isCardSuc unfolding isCardSuc_def by blast


lemma cardSuc_ordLeq:
"Card_order r \<Longrightarrow> r \<le>o cardSuc r"
using cardSuc_greater ordLeq_iff_ordLess_or_ordIso by blast


text{* The minimality property of @{text "cardSuc"} originally present in its definition 
is local to the type @{text "'a set rel"}, i.e., that of @{text "cardSuc r"}:  *}

lemma cardSuc_least_aux: 
"\<lbrakk>Card_order (r::'a rel); Card_order (r'::'a set rel); r <o r'\<rbrakk> \<Longrightarrow> cardSuc r \<le>o r'"
using cardSuc_isCardSuc unfolding isCardSuc_def by blast


text{* But from this we can infer general minimality: *}

lemma cardSuc_least: 
assumes CARD: "Card_order r" and CARD': "Card_order r'" and LESS: "r <o r'"
shows "cardSuc r \<le>o r'"
proof-
  let ?p = "cardSuc r"
  have 0: "Well_order ?p \<and> Well_order r'"
  using assms cardSuc_Card_order unfolding card_order_on_def by blast
  {assume "r' <o ?p"
   then obtain r'' where 1: "Field r'' < Field ?p" and 2: "r' =o r'' \<and> r'' <o ?p"
   using internalize_ordLess[of r' ?p] by blast
   (*  *)
   have "Card_order r''" using CARD' Card_order_ordIso2 2 by blast
   moreover have "r <o r''" using LESS 2 ordLess_ordIso_trans by blast
   ultimately have "?p \<le>o r''" using cardSuc_least_aux CARD by blast 
   hence False using 2 not_ordLess_ordLeq by blast 
  } 
  thus ?thesis using 0 ordLess_or_ordLeq by blast
qed


lemma Field_cardSuc_not_empty:
assumes "Card_order r"
shows "Field (cardSuc r) \<noteq> {}"
proof
  assume "Field(cardSuc r) = {}"
  hence "|Field(cardSuc r)| \<le>o r" using assms Card_order_empty[of r] by auto
  hence "cardSuc r \<le>o r" using assms card_of_Field_ordIso 
  cardSuc_Card_order ordIso_symmetric ordIso_ordLeq_trans by blast
  thus False using cardSuc_greater not_ordLess_ordLeq assms by blast
qed


lemma cardSuc_ordLess_ordLeq: 
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r <o r') = (cardSuc r \<le>o r')"
proof(auto simp add: assms cardSuc_least)
  assume "cardSuc r \<le>o r'"
  thus "r <o r'" using assms cardSuc_greater ordLess_ordLeq_trans by blast
qed


lemma cardSuc_ordLeq_ordLess: 
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r' \<le>o r) = (r' <o cardSuc r)"
proof-
  have "Well_order r \<and> Well_order r'"
  using assms unfolding card_order_on_def by auto
  moreover have "Well_order(cardSuc r)"
  using assms cardSuc_Card_order card_order_on_def by blast
  ultimately show ?thesis 
  using assms cardSuc_ordLess_ordLeq[of r r'] 
  ordLess_iff_not_ordLeq[of r r'] ordLess_iff_not_ordLeq[of r' "cardSuc r"] by blast
qed


lemma cardSuc_mono_ordLeq:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r \<le>o r') = (cardSuc r \<le>o cardSuc r')"
using assms cardSuc_ordLeq_ordLess cardSuc_ordLess_ordLeq cardSuc_Card_order by blast


lemma cardSuc_mono_ordLess:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r <o r') = (cardSuc r <o cardSuc r')"
proof-
  have 0: "Well_order r \<and> Well_order r' \<and> Well_order(cardSuc r) \<and> Well_order(cardSuc r')"
  using assms by (auto simp add: card_order_on_def cardSuc_Well_order) 
  thus ?thesis 
  using ordLess_iff_not_ordLeq[of r r'] ordLess_iff_not_ordLeq
  using cardSuc_mono_ordLeq[of r' r] assms by blast
qed


lemma cardSuc_invar_ordIso:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r =o r') = (cardSuc r =o cardSuc r')"
proof-
  have 0: "Well_order r \<and> Well_order r' \<and> Well_order(cardSuc r) \<and> Well_order(cardSuc r')"
  using assms by (auto simp add: card_order_on_def cardSuc_Well_order) 
  thus ?thesis 
  using ordIso_iff_ordLeq[of r r'] ordIso_iff_ordLeq
  using cardSuc_mono_ordLeq[of r r'] cardSuc_mono_ordLeq[of r' r] assms by blast
qed


lemma embed_implies_ordIso_Restr:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and EMB: "embed r' r f" 
shows "r' =o Restr r (f ` (Field r'))"
using assms embed_implies_iso_Restr Well_order_Restr unfolding ordIso_def by blast


lemma cardSuc_natLeq_on_Suc:
"cardSuc(natLeq_on n) =o natLeq_on(Suc n)"
proof-
  obtain r r' p where r_def: "r = natLeq_on n" and 
                      r'_def: "r' = cardSuc(natLeq_on n)"  and  
                      p_def: "p = natLeq_on(Suc n)" by blast
  (* Preliminary facts:  *)
  have CARD: "Card_order r \<and> Card_order r' \<and> Card_order p" unfolding r_def r'_def p_def 
  using cardSuc_ordLess_ordLeq natLeq_on_Card_order cardSuc_Card_order by blast
  hence WELL: "Well_order r \<and> Well_order r' \<and>  Well_order p"
  unfolding card_order_on_def by force
  have FIELD: "Field r = {0..<n} \<and> Field p = {0..<(Suc n)}" 
  unfolding r_def p_def Field_natLeq_on by simp
  hence FIN: "finite (Field r)" by force
  have "r <o r'" using CARD unfolding r_def r'_def using cardSuc_greater by blast
  hence "|Field r| <o r'" using CARD card_of_Field_ordIso ordIso_ordLess_trans by blast
  hence LESS: "|Field r| <o |Field r'|" 
  using CARD card_of_Field_ordIso ordLess_ordIso_trans ordIso_symmetric by blast
  (* Main proof: *)
  have "r' \<le>o p" using CARD unfolding r_def r'_def p_def
  using natLeq_on_ordLeq_less cardSuc_ordLess_ordLeq by blast
  moreover have "p \<le>o r'"
  proof- 
    {assume "r' <o p" 
     then obtain f where 0: "embedS r' p f" unfolding ordLess_def by force
     let ?q = "Restr p (f ` Field r')"
     have 1: "embed r' p f" using 0 unfolding embedS_def by force
     hence 2: "f ` Field r' < {0..<(Suc n)}" 
     using WELL FIELD 0 by (auto simp add: embedS_iff)    
     have "ofilter p (f ` Field r')" using embed_Field_ofilter 1 WELL by blast
     then obtain m where "m \<le> Suc n" and 3: "f ` (Field r') = {0..<m}" 
     unfolding p_def by (auto simp add: natLeq_on_ofilter_iff)
     hence 4: "m \<le> n" using 2 by force
     (*  *)
     have "bij_betw f (Field r') (f ` (Field r'))"
     using 1 WELL embed_inj_on unfolding bij_betw_def by force
     moreover have "finite(f ` (Field r'))" using 3 finite_atLeastLessThan[of 0 m] by force
     ultimately have 5: "finite (Field r') \<and> card(Field r') = card (f ` (Field r'))"
     using bij_betw_imp_card bij_betw_finite by blast
     hence "card(Field r') \<le> card(Field r)" using 3 4 FIELD by force
     hence "|Field r'| \<le>o |Field r|" using FIN 5 finite_card_of_iff_card2 by blast 
     hence False using LESS not_ordLess_ordLeq by auto
    } 
    thus ?thesis using WELL CARD by (auto simp add: ordLess_iff_not_ordLeq)
  qed 
  ultimately show ?thesis using ordIso_iff_ordLeq unfolding r'_def p_def by blast
qed


lemma card_of_cardSuc_finite: 
"finite A = finite(Field(cardSuc |A| ))"
proof
  assume *: "finite (Field (cardSuc |A| ))"
  have 0: "|Field(cardSuc |A| )| =o cardSuc |A|"
  using card_of_Card_order cardSuc_Card_order card_of_Field_ordIso by blast
  hence "|A| \<le>o |Field(cardSuc |A| )|"
  using card_of_Card_order[of A] cardSuc_ordLeq[of "|A|"] ordIso_symmetric 
  ordLeq_ordIso_trans by blast
  thus "finite A" using * card_of_ordLeq_finite by blast
next
  assume "finite A"
  then obtain n where "|A| =o natLeq_on n" using finite_iff_card_of_natLeq_on by blast
  hence "cardSuc |A| =o cardSuc(natLeq_on n)" 
  using card_of_Card_order cardSuc_invar_ordIso natLeq_on_Card_order by blast
  hence "cardSuc |A| =o natLeq_on(Suc n)" 
  using cardSuc_natLeq_on_Suc ordIso_transitive by blast
  hence "cardSuc |A| =o |{0..<(Suc n)}|" using card_of_less ordIso_equivalence by blast
  moreover have "|Field (cardSuc |A| ) | =o cardSuc |A|" 
  using card_of_Field_ordIso cardSuc_Card_order card_of_Card_order by blast
  ultimately have "|Field (cardSuc |A| ) | =o |{0..<(Suc n)}|" 
  using ordIso_equivalence by blast
  thus "finite (Field (cardSuc |A| ))" 
  using card_of_ordIso_finite finite_atLeastLessThan by blast
qed

end
