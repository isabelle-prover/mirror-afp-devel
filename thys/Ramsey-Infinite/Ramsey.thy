header "Ramsey's Theorem"

theory Ramsey = Main:

text {* The following is taken from Boolos and Jeffrey "Computability
and Logic", 3rd edition, Ch. 26 on Ramsey's theorem. This is the
mechanisation of the infinitary version of the theorem. We have
modified the proof slightly so that we have a slightly stronger
hypothesis. In particular, we strengthen the induction hypothesis to
hold for any infinite subset of the naturals. This avoids the rather
peculiar mapping argument between kj and aikj on p.263, which is
unnecessary and slightly spoils what is a really beautiful result. *}

ML {* Pretty.setmargin 160;; *}

subsection "Library rules, or variants thereof"

lemma insert_id: "x \<in> X ==> insert x X = X" apply(force) done

lemma skolem: "\<forall>x. \<exists>y. P x y ==> \<exists>Y. \<forall>x. P x (Y x)"
 apply(rule Hilbert_Choice.choice)
 .

lemma nat_LeastI_ex: "\<exists>x. P (x::nat) ==> P (LEAST x. P x)" 
  apply(erule exE)
  apply(rule_tac P=P in LeastI) 
  .

lemma not_nil_least_mem: "X ~= {} ==> (LEAST x. (x::nat) \<in> X) \<in> X" 
  apply(rule_tac P="% x. (x::nat) \<in> X" in nat_LeastI_ex) apply(force) done 

lemma not_nil_least_decompose: "(X::nat set) ~= {} ==> insert (LEAST x. x \<in> X) (X - {(LEAST x. x \<in> X)}) = X"
  apply(blast intro: not_nil_least_mem)
  done

lemma least_lemma: "(X::nat set) ~= {} ==> x \<in> X - {LEAST x. x \<in> X} ==> (LEAST x. x \<in> X) < x"
  apply(simp) apply(elim conjE)
  apply(subgoal_tac "(LEAST x. x \<in> X) \<le> x")
  apply(force)
  apply(rule Least_le)
  .

lemma card_diff: "(X::nat set) ~= {} ==> finite X ==> card X = Suc n ==> x \<in> X ==> card (X - {x}) = n"
  apply(subgoal_tac "finite (X - {x})")
  apply(frule_tac card_insert[of "(X - {x})" "x"])
  apply(simp add: insert_id)
  apply(force)
  done

lemma card_Suc_decompose:
     "finite (X::nat set) ==> card X = Suc n ==> 
      \<exists>X'. X = insert (LEAST x. x \<in> X) X' & finite X' & card X' = n & 
           (\<forall>x \<in> X'. (LEAST x. x \<in> X) < x)" 
  apply(rule_tac x="X - {LEAST x. x \<in> X}" in exI)
  apply(subgoal_tac "(LEAST x. x \<in> X) \<in> X") prefer 2 apply(rule not_nil_least_mem) apply(force)
  apply(intro conjI)
     apply(force)
    apply(force)
   apply(rule card_diff) apply(force) apply(assumption) apply(assumption) apply(rule not_nil_least_mem) apply(force)
  apply(rule)
  apply(rule least_lemma)
  apply(force) .

lemma mem_mem_image: "x \<in> X ==> f x \<in> f ` X" by blast
  
lemma image_inj: "[| finite (X::nat set); X \<subseteq> f ` I; inj_on f I |] 
  ==> \<exists>I'. (I'\<subseteq> I) & (finite I') & (X = f ` I') & (card I' = card X)" 
  apply(induct X rule: finite_induct)
   apply(rule_tac x="{}" in exI) apply(force)
  apply(simp)
  apply(erule exE)
  apply(elim conjE)
  apply(subgoal_tac "\<exists>i \<in> I. f i = x") prefer 2 apply(force)
  apply(erule bexE)
  apply(subgoal_tac "i ~: I'") prefer 2 apply(rule ccontr) apply(simp) apply(subgoal_tac "f i \<in> f ` I'") apply(force) apply(rule mem_mem_image) apply(assumption)
  apply(rule_tac x="insert i I'" in exI)
  by force

lemma inj_on_subset: "inj_on f A ==> B \<subseteq> A ==> inj_on f B" apply(simp only: inj_on_def) by blast

lemma inj_inj_on: "inj f ==> inj_on f A" by(force intro: inj_on_subset)



subsection "Infinite sets"

lemma infinite_infinite_sub: "infinite Y ==> infinite (Y - {x})" by force

lemma infinite_least_mem: "infinite (Y::nat set) ==> (LEAST x. x \<in> Y) \<in> Y" 
  apply(rule not_nil_least_mem) 
  by force

lemma infinite_subset_exists[rule_format]: "!(X::nat set). infinite X --> (\<exists>X'. finite X' & X' \<subseteq> X & card X' = n)"
  apply(induct_tac n)
   apply(force)
  apply(rule) apply(rule)
  apply(drule_tac x="X - {LEAST x . x \<in> X}" in spec)
  apply(erule impE) apply(force)
  apply(erule exE)
  apply(elim conjE)
  apply(rule_tac x="insert (LEAST x. x \<in> X) X'" in exI)
  apply(intro conjI)
    apply(force)
   apply(subgoal_tac "(LEAST x . x \<in> X) \<in> X") apply(force) apply(force intro: infinite_least_mem)
  apply(force)
  done

lemma infinite_inj_infinite_image: "infinite Z ==> inj_on f Z ==> infinite (f ` Z)"
  apply(rule ccontr)
  apply(simp)
  apply(force dest: finite_imageD)
  done
  

subsection "tinv"

constdefs tinv :: "'a set => ('a => 'b) => 'b => 'a set"
  "tinv A f b == {a. a \<in> A & f a = b}"

  -- "have a function f from A to B, with finite B, but inf A"

lemma UN_range_tinv_eq_domain: "(\<Union>b \<in> (f ` A). tinv A f b) = A"
  apply(simp add: tinv_def)
  by blast

lemma tinv_infinite_finite: "infinite A ==> finite (f ` A) ==> (\<exists>b \<in> (f ` A). infinite (tinv A f b))"
  apply(rule ccontr)
  apply(simp) -- "can't access bex simps 9 to delete"
  apply(subgoal_tac "\<forall>b \<in> (f ` A). finite (tinv A f b)")
  apply(thin_tac "\<forall>b\<in>A. finite (tinv A f (f b))")
  apply(simp only: finite_UN[symmetric])
  apply(simp only: UN_range_tinv_eq_domain)
  by simp

thm tinv_infinite_finite[simplified tinv_def]


subsection "Definitions"

consts
  s :: "nat"

  -- "predicate on functions-- basically f is a partition of size r subsets of Y into s disjoint classes"

constdefs
  fpred :: "(nat set => nat) => nat set =>  nat => bool"
  "fpred f Y r == \<forall>x. finite x & x \<subseteq> Y & card x = r --> f x < s"

lemma fpred_fpred_subset: "fpred f Y r ==> Y' \<subseteq> Y ==> fpred f Y' r"
  apply(simp add: fpred_def)
  apply(blast)
  done

lemma fpred_Suc_fpred: "[| infinite Y; fpred f Y (Suc n); z \<in> Y |] ==> fpred (\<lambda>x. f (insert z x)) (Y - {z}) n" 
  apply(simp add: fpred_def) 
  apply(rule)
  apply(rule) apply(elim conjE)
  apply(drule_tac x="insert z x" in spec)
  apply(erule impE) apply(force)
  apply(force)
  done

constdefs pbi :: "nat set => nat"
  "pbi == % Yi. LEAST x. x \<in> Yi"

constdefs pY2i :: "nat set => nat set"
  "pY2i Yi == let bi = pbi Yi in Yi - {bi}"

constdefs pfi :: "(nat set => nat) => nat set => (nat set => nat)"
  "pfi f Yi == (
  let bi = pbi Yi in
  (% x. f (insert bi x)))"

constdefs pWi :: "(nat set * (nat set => nat) => (nat set * nat))
  => (nat set => nat) 
  => nat set 
  => nat set"
  "pWi Theta f Yi == (
  let Y2i = pY2i Yi in
  let fi = pfi f Yi in
  fst (Theta (Y2i, fi)))"

constdefs pji :: "(nat set * (nat set => nat) => (nat set * nat))
  => (nat set => nat) 
  => nat set 
  => nat"
  "pji Theta f Yi == (
  let Y2i = pY2i Yi in
  let fi = pfi f Yi in
  snd (Theta (Y2i, fi)))"
  
consts Yis :: "(nat set * (nat set => nat) => (nat set * nat))
  => (nat set => nat) 
  => nat set 
  => nat
  => nat set"
primrec
  "Yis Theta f Yinit 0 = Yinit"
  "Yis Theta f Yinit (Suc i) = 
  (let Yi = Yis Theta f Yinit i in
  pWi Theta f Yi)"


constdefs assum :: "nat => (nat set * (nat set => nat) => (nat set * nat)) => bool"
  "assum n Theta ==  \<forall>ab. infinite (fst ab) \<and> fpred (snd ab) (fst ab) n \<longrightarrow> (let (W, j) = Theta ab in W \<subseteq> (fst ab) \<and> infinite W \<and> (\<forall>X. finite X \<and> X \<subseteq> W \<and> card X = n \<longrightarrow> (snd ab) X = j))"


subsection "Main lemmas about definitions"

lemma horiz_pWi: "[| 
  assum n Theta;
  fpred f Yi (Suc n);
  infinite Yi
  |] ==> infinite (pWi Theta f Yi) & (pWi Theta f Yi) \<subseteq> Yi - {pbi Yi}"
  apply(simp add: assum_def)
  apply(simp add: pWi_def Let_def pbi_def pY2i_def pfi_def pji_def)
  apply(drule_tac x="(Yi - {LEAST x. x \<in> Yi})" in spec)
  apply(drule_tac x=" \<lambda>x. f (insert (LEAST x. x \<in> Yi) x)" in spec)
  apply(erule impE)
   apply(rule)
    apply(rule infinite_infinite_sub) apply(assumption)
   apply(rule fpred_Suc_fpred) apply(assumption) apply(assumption) apply(rule infinite_least_mem) apply(assumption)
  apply(clarsimp)
  done
  
lemma horiz_pji: assumes assums: "assum n Theta" "fpred f Yi (Suc n)" "infinite Yi"
  shows "(\<forall>X. finite X \<and> X \<subseteq> (pWi Theta f Yi) \<and> card X = n \<longrightarrow> (f (insert (pbi Yi) X) = (pji Theta f Yi)))
  & pji Theta f Yi < s"
  using assums
  apply(simp add: assum_def)
  apply(simp add: pWi_def Let_def pbi_def pY2i_def pfi_def pji_def)
  apply(drule_tac x="(Yi - {LEAST x. x \<in> Yi})" in spec)
  apply(drule_tac x=" \<lambda>x. f (insert (LEAST x. x \<in> Yi) x)" in spec)
  apply(erule impE)
   apply(rule)
    apply(rule infinite_infinite_sub) apply(assumption)
   apply(rule fpred_Suc_fpred) apply(assumption) apply(assumption) apply(rule infinite_least_mem) apply(assumption)
  apply(clarsimp)

  apply(subgoal_tac "\<exists>X. finite X & X \<subseteq> (pWi Theta f Yi) & card X = n") 
   apply(erule exE)
   apply(drule_tac x=X in spec)   
   apply(erule impE) apply(intro conjI) apply(force) apply(simp add: pWi_def Let_def pY2i_def pfi_def pbi_def) apply(force)
  
   apply(insert horiz_pWi[OF assums])

   apply(simp only: fpred_def) apply(drule_tac x="(insert (LEAST x. x \<in> Yi) X)" in spec) apply(erule impE)
    apply(intro conjI) apply(force) apply(subgoal_tac "(LEAST x. x \<in> Yi) \<in> Yi & X \<subseteq> Yi") apply(force)
     apply(rule) apply(rule infinite_least_mem) apply(assumption) apply(force)
    apply(simp add: pbi_def) apply(force)
   apply(force)
  apply(rule infinite_subset_exists)
  apply(force)
  done


  -- "Locale for readability"

locale l =
  fixes Theta and f and Y
  and Yi and bi and Y2i and fi and Wi and ji
  defines "Yi == (Yis Theta f Y)"
  and "bi == (pbi o Yi)"
  and "Y2i == (pY2i o Yi)"
  and "fi == (pfi f o Yi)"
  and "Wi == (pWi Theta f o Yi)"
  and "ji == (pji Theta f o Yi)"
  notes[simp] = Yi_def bi_def Y2i_def fi_def Wi_def ji_def

lemma (in l) vert: "[|
  assum n Theta;
  fpred f Y (Suc n);
  infinite Y 
  |] ==> (Yi i) \<subseteq> Y & infinite (Yi i)"
  apply(induct_tac i)
   apply(simp)
  apply(elim conjE)
  apply(frule_tac Yi="Yis Theta f Y na" in horiz_pWi) apply(rule fpred_fpred_subset) apply(assumption)
apply (auto simp add: Let_def)  
  done

lemma (in l) horiz2: "[| 
  assum n Theta;
  fpred f Y (Suc n);
  infinite Y
  |] ==> infinite (Wi i) 
  & (Wi i) \<subseteq> (Yi i) - {bi i} 
  & (\<forall>X. finite X \<and> X \<subseteq> (Wi i) \<and> card X = n \<longrightarrow> (f (insert (bi i) X) = (ji i)))
  & ji i < s"
  apply(frule_tac i=i in vert) apply(assumption) apply(assumption) apply(elim conjE)
  apply(frule_tac Yi="Yi i" in horiz_pWi) apply(rule fpred_fpred_subset) apply(assumption) apply(assumption) apply(assumption)
  apply(frule_tac Yi="Yi i" in horiz_pji) apply(rule fpred_fpred_subset) apply(assumption) apply(assumption) apply(assumption)
  apply(simp)
  done


subsection "Yi lemmas"

lemma (in l) Yi_Suc: "[|
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y
  |] ==> \<forall>x. x \<in> Yi (Suc a) \<longrightarrow> bi a < x"
  apply(frule_tac i=a in horiz2) apply(assumption+) apply(elim conjE)
  apply(simp add: pbi_def Let_def)
  apply(rule)
  apply(rule)
  apply(subgoal_tac "x \<in> Yis Theta f Y a - {LEAST x. x \<in> Yis Theta f Y a}") defer apply(force)
  apply(rule least_lemma) apply(force) apply(force) done
  
lemma (in l) mono_Yi': "[|
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y
  |] ==> Yi (a+b) \<subseteq> Yi a"
  apply(induct_tac b)
  apply(simp)
  apply(rule subset_trans) prefer 2 apply(assumption)
  apply(simp)
  apply(simp add: Let_def)
  using horiz2 apply(force)
  done

lemma (in l) mono_Yi: 
  "[| assum n Theta;
      fpred f Y (Suc n); 
      infinite Y
  |] ==> a \<le> b ==> Yi b \<le> Yi a"
  apply(subgoal_tac "\<exists>ba. b = a + ba")
  apply(erule exE)
  apply(simp only:)
  apply(rule mono_Yi') apply(assumption+)
  by arith


subsection "pbi lemmas"

lemma (in l) range_pbi_subset_Y: "[|
  assum n Theta;
  fpred f Y (Suc n);
  infinite Y
  |] ==> range bi \<subseteq> Y"
  apply(simp add: pbi_def)
  apply(clarsimp)
  apply(frule_tac i=xa in vert) apply(assumption, assumption)
  apply(elim conjE)
  apply(subgoal_tac "(LEAST x. x \<in> Yis Theta f Y xa) \<in> Yis Theta f Y xa")
  apply(force)
  apply(force intro: infinite_least_mem) 
  done

lemma (in l) bi_Yi: "[|
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y
  |] ==> bi i \<in> Yi i"
  apply(simp add: pbi_def)
  apply(rule infinite_least_mem)
  using vert
  apply(force)
  done

lemma (in l) mono_pbi: "[|
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y
  |] ==> \<forall>a b. a < b --> (bi a < bi b)"
  apply(rule)
  apply(rule)
  apply(rule)
  apply(subgoal_tac "bi b \<in> Yi b & Yi b \<subseteq> Yi (Suc a) & (\<forall>x. x \<in> Yi (Suc a) --> bi a < x)")
   apply(force)
  apply(intro conjI)
    apply(rule bi_Yi) apply(assumption+)
   apply(subgoal_tac "Suc a \<le> b") apply(rule mono_Yi) apply(assumption+)
   apply(force)
  apply(rule Yi_Suc)
  .

lemma (in l) pbi_inj: "\<lbrakk>
  assum n Theta; 
  fpred f Y (Suc n);
  infinite Y
  \<rbrakk>
  \<Longrightarrow> inj bi"
  apply(frule_tac mono_pbi) apply(assumption+)
  apply(simp only: inj_on_def)
  apply clarify 
  apply(cut_tac x=x and y=y in linorder_less_linear)
  apply(force)
  done

lemma (in l) infinite_pbi_on_infinite: "\<lbrakk>
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y;
  infinite Z\<rbrakk>
  \<Longrightarrow> infinite (bi ` Z)"
  apply(frule_tac pbi_inj) apply(assumption) apply(assumption)
  apply(rule infinite_inj_infinite_image)
  by (auto simp: inj_inj_on)


subsection "ji lemmas"

lemma (in l) range_ji: "[|
  assum n Theta;
  fpred f Y (Suc n); 
  infinite Y
  |] ==> finite (range ji)"
  apply(rule_tac B= "{..s(}" in finite_subset)
  using horiz2 apply(force)
  apply(force)
  done


subsection "Main lemma"

lemma (in l) main: 
  assumes assums: "assum n Theta" "fpred f Y (Suc n)" "infinite Y"
  and I: "I = {i. ji i = b}" "infinite I"
  and finX: "finite X"
  and X: "X \<subseteq> bi ` I"
  and cardX: "card X = Suc n"
  shows "f X = b"
proof -

  from pbi_inj[OF assums] have inj_pbi: "inj bi" .
  hence inj_pbi': "inj_on bi I" by(rule inj_inj_on)

  from image_inj[OF finX X inj_pbi'] obtain J 
    where JI: "J \<subseteq> I"
    and finJ: "finite J"
    and XJ: "X = bi ` J"
    and cardJ: "card J = Suc n"
    by (auto simp: cardX)

  def minj == "(LEAST j. j \<in> J)"

  from cardJ have minj: "minj \<in> J" 
    apply(simp add: minj_def)
    apply(rule not_nil_least_mem)
    by force
  
  from card_Suc_decompose[OF finJ cardJ] obtain J' where  
    JJ': "J = insert minj J'"
    and finJ': "finite J'"
    and cardJ': "card J' = n"
    and minjJ': "(\<forall>i \<in> J'. minj < i)" by (force simp add: minj_def)
  
  def minx == "bi minj"

  from XJ JJ' have minx: "minx \<in> X" by(simp add: minx_def)

  def X' == "bi ` J'"

  from inj_pbi finJ' cardJ' have cardX': "card X' = n"
    apply(subgoal_tac "inj_on bi J'")
    apply(simp add: X'_def card_image) 
    by (force simp: inj_inj_on)

  from XJ JJ' have XX': "X = insert minx X'" by(simp add: X'_def minx_def)

  from XX' finX have finX': "finite X'" by force

  from minjJ' mono_pbi[OF assums] have "\<forall>x \<in> X'. minx < x" by(simp add: X'_def minx_def)

  hence minx_def_2: "minx = (LEAST x. x \<in> X)" 
    apply(subst XX') 
    apply(rule sym)
    apply(rule Least_equality)
    by auto

  from minx have X_def_2: "X = insert minx (X - {minx})" by(force)

  have "\<forall>x \<in> X'. x \<in> Yi (Suc minj)"
  proof
    fix x assume x: "x \<in> X'"
    then obtain j' where j':"j' \<in> J' & x = bi j'" by(force simp: X'_def)
    with minjJ' have "minj < j'" by force
    hence "Suc minj \<le> j'" by force
    from mono_Yi[OF assums this] have "Yi j' \<subseteq> Yi (Suc minj)" .
    also have "x \<in> Yi j'" 
      apply(simp only: j')
      by(rule bi_Yi[OF assums])
    finally show "x \<in> Yi (Suc minj)" .
  qed
  
  hence "\<forall>x \<in> X'. x \<in> (Wi minj)" by(simp add: Let_def)

  hence "X' \<subseteq> (Wi minj)" by force

  with horiz2[OF assums, of minj] finX' cardX' have "f (insert (bi minj) X') = (ji minj)" by force 

  also from JJ' JI I have "... = b" by(force)

  finally have "f (insert (bi minj) X') = b" .

  also have "(insert (bi minj) X') = X" by(simp add: minx_def XX')

  finally show "f X = b" by force

qed


subsection "Ramsey's theorem"

  -- "strong form"

lemma ramsey':
  "(\<exists>Theta. \<forall>Yf . infinite (fst Yf) & fpred (snd Yf) (fst Yf) r --> 
  (let (W,j) = Theta Yf in W \<subseteq> (fst Yf) & infinite W  & 
  (\<forall>X. finite X & X \<subseteq> W & card X = r --> ((snd Yf) X = j))))"
  apply(rule_tac nat_induct)
   apply(rule_tac x="% (y, g). (y, g {})"  in exI)
   apply(rule)
   apply(simp add: Let_def) 
   apply(force)

  apply(erule exE)
  apply(rule skolem)
  apply(fold assum_def)
  apply(rule)
  apply(case_tac Yf, rename_tac Y f)
  
  apply(clarsimp)
  apply(subgoal_tac "infinite (UNIV::nat set) & finite ( (pji Theta f o (Yis Theta f Y))` UNIV )")
   apply(elim conjE)
   apply(frule_tac A="UNIV::nat set" in tinv_infinite_finite) apply(assumption)
   apply(erule bexE) apply(simp add: tinv_def)
   apply(subgoal_tac "\<exists>I. I = {i. (pji Theta f o (Yis Theta f Y)) i = b}") prefer 2 apply(force)
   apply(erule exE)

   -- "the infinite set we have here is the set of i st pji = b"

   apply(rule_tac x="(pbi \<circ> Yis Theta f Y) ` I" in exI)
   apply(rule_tac x="b" in exI)
   apply(simp add: Let_def)
   apply(intro conjI)
     apply(subgoal_tac "range (pbi \<circ> Yis Theta f Y) \<subseteq> Y") apply(force)
     apply(rule l.range_pbi_subset_Y) apply(assumption) apply(assumption) apply(assumption) 
    apply(rule l.infinite_pbi_on_infinite) apply(assumption) apply(assumption) apply(assumption) apply(assumption)
   apply(rule) apply(rule) apply(elim conjE)
   -- "this is the real goal"

   apply(rule l.main) apply(assumption) apply(assumption) apply(assumption) apply(simp) apply(simp) apply(assumption) apply(force) apply(assumption)

  apply(rule)
   apply(force)
  apply(rule l.range_ji)
  .

  -- "standard form"
  
theorem ramsey:
  "infinite Y ==> fpred f Y r ==> \<exists>Y'. Y' \<subseteq> Y & infinite Y' & (\<exists>j. (\<forall>X. finite X \<and> X \<subseteq> Y' \<and> card X = r \<longrightarrow> f X = j))"
  apply(insert ramsey'[of r])
  apply(erule exE)
  apply(drule_tac x="(Y,f)" in spec)
  apply(simp add: Let_def)
  apply(case_tac "(Theta (Y, f))")
  apply auto
  done

end

