section "Formula"

theory Formula
  imports Base 
begin

subsection "Variables"

datatype vbl = X nat
  \<comment> \<open>FIXME there's a lot of stuff about this datatype that is
  really just a lifting from nat (what else could it be). Makes me
  wonder whether things wouldn't be clearer is we just identified vbls
  with nats\<close>

primrec deX :: "vbl \<Rightarrow> nat" where "deX (X n) = n"

lemma X_deX[simp]: "X (deX a) = a"
  by(cases a) simp

definition "zeroX = X 0"

primrec
  nextX :: "vbl \<Rightarrow> vbl" where
  "nextX (X n) = X (Suc n)"

definition
  vblcase :: "['a,vbl \<Rightarrow> 'a,vbl] \<Rightarrow> 'a" where
  "vblcase a f n \<equiv> (@z. (n=zeroX \<longrightarrow> z=a) \<and> (!x. n=nextX x \<longrightarrow> z=f(x)))"

declare [[case_translation vblcase zeroX nextX]]

definition
  freshVar :: "vbl set \<Rightarrow> vbl" where
  "freshVar vs = X (LEAST n. n \<notin> deX ` vs)"
    
lemma nextX_nextX[iff]: "nextX x = nextX y = (x = y)"
  by (metis Suc_inject nextX.simps vbl.exhaust vbl.inject)

lemma inj_nextX: "inj nextX"
  by(auto simp add: inj_on_def)

lemma ind: 
  assumes "P zeroX" "\<And> v. P v \<Longrightarrow> P (nextX v)"
  shows "P v'"
proof -
  have "P (X n)" for n
    by (induction n) (use assms zeroX_def nextX_def in force)+
  then show ?thesis
    by (metis X_deX)
qed

lemma zeroX_nextX[iff]: "zeroX \<noteq> nextX a"
  by (metis nat.discI nextX.simps vbl.exhaust vbl.inject zeroX_def)

lemmas nextX_zeroX[iff] = not_sym[OF zeroX_nextX]

lemma nextX: "nextX (X n) = X (Suc n)"
  by simp

lemma vblcase_zeroX[simp]: "vblcase a b zeroX = a" 
  by(simp add: vblcase_def)

lemma vblcase_nextX[simp]: "vblcase a b (nextX n) = b n" 
  by(simp add: vblcase_def)

lemma vbl_cases: "x = zeroX \<or> (\<exists>y. x = nextX y)"
  by (metis X_deX nextX old.nat.exhaust zeroX_def)

lemma vbl_casesE: "\<lbrakk> x = zeroX \<Longrightarrow> P; \<And> y. x = nextX y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using vbl_cases by blast

lemma comp_vblcase: "f \<circ> vblcase a b = vblcase (f a) (f \<circ> b)"
proof
  fix x
  show "(f \<circ> vblcase a b) x = (case x of zeroX \<Rightarrow> f a | nextX x \<Rightarrow> (f \<circ> b) x)"
    using vbl_cases [of x] by auto
qed

lemma equalOn_vblcaseI': "equalOn (preImage nextX A) f g \<Longrightarrow> equalOn A (vblcase x f) (vblcase x g)"
  unfolding equalOn_def
  by (metis vbl_casesE vblcase_nextX vblcase_zeroX vimageI2) 
    
lemma equalOn_vblcaseI: "(zeroX \<in> A \<Longrightarrow> x=y) \<Longrightarrow> equalOn (preImage nextX A) f g \<Longrightarrow> equalOn A (vblcase x f) (vblcase y g)"
  by (smt (verit) equalOnD equalOnI equalOn_vblcaseI' vbl_casesE vblcase_nextX)

lemma X_deX_connection: "X n \<in> A = (n \<in> (deX ` A))"
  by force

lemma finiteFreshVar: "finite A \<Longrightarrow> freshVar A \<notin> A"
  unfolding freshVar_def
  by (metis (no_types, lifting) LeastI_ex X_deX finite_imageI
      finite_nat_set_iff_bounded image_eqI order_less_imp_triv
      vbl.inject)

lemma freshVarI: "\<lbrakk>finite A; B \<subseteq> A\<rbrakk> \<Longrightarrow> freshVar A \<notin> B"
  using finiteFreshVar in_mono by blast

lemma freshVarI2: "\<lbrakk>finite A; \<And>x . x \<notin> A \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (freshVar A)"
  using finiteFreshVar by presburger

lemmas vblsimps = vblcase_zeroX vblcase_nextX zeroX_nextX
  nextX_zeroX nextX_nextX comp_vblcase


subsection "Predicates"

datatype predicate = Predicate nat

datatype signs = Pos | Neg

primrec sign :: "signs \<Rightarrow> bool \<Rightarrow> bool"
  where
    "sign Pos x = x"
  | "sign Neg x = (\<not> x)"

primrec invSign :: "signs \<Rightarrow> signs"
  where
    "invSign Pos = Neg"
  | "invSign Neg = Pos"


subsection "Formulas"

datatype formula =
  FAtom signs predicate "(vbl list)"
  | FConj signs formula formula
  | FAll  signs formula  


subsection "formula signs induct, formula signs cases"

lemma formula_signs_induct [case_names FAtomP FAtomN FConjP FConjN FAllP FAllN, cases type: formula]: 
  "\<lbrakk>\<And>p vs. P (FAtom Pos p vs);
  \<And>p vs. P (FAtom Neg p vs);
  \<And>A B  . \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (FConj Pos A B);
  \<And>A B  . \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (FConj Neg A B);
  \<And>A    . \<lbrakk>P A\<rbrakk> \<Longrightarrow> P (FAll  Pos A); 
  \<And>A    . \<lbrakk>P A\<rbrakk> \<Longrightarrow> P (FAll  Neg A) 
 \<rbrakk> \<Longrightarrow> P A"
  by (induct A; rule signs.induct; force)

    \<comment> \<open>induction using nat induction, not wellfounded induction\<close>

lemma sizelemmas: "size A < size (FConj z A B)"
  "size B < size (FConj z A B)"
  "size A < size (FAll  z A)"
  by auto

primrec FNot :: "formula \<Rightarrow> formula"
  where
    FNot_FAtom: "FNot (FAtom z P vs)  = FAtom (invSign z) P vs"
  | FNot_FConj: "FNot (FConj z A0 A1) = FConj (invSign z) (FNot A0) (FNot A1)"    
  | FNot_FAll:  "FNot (FAll  z body)  = FAll  (invSign z) (FNot body)"

primrec neg  :: "signs \<Rightarrow> signs"
  where
    "neg Pos = Neg"
  | "neg Neg = Pos"

primrec
  dual :: "[(signs \<Rightarrow> signs),(signs \<Rightarrow> signs),(signs \<Rightarrow> signs)] \<Rightarrow> formula \<Rightarrow> formula"
  where
    dual_FAtom: "dual p q r (FAtom z P vs)  = FAtom (p z) P vs"
  | dual_FConj: "dual p q r (FConj z A0 A1) = FConj (q z) (dual p q r A0) (dual p q r A1)"
  | dual_FAll:  "dual p q r (FAll  z body)  = FAll  (r z) (dual p q r body)"

lemma dualCompose: "dual p q r \<circ> dual P Q R = dual (p \<circ> P) (q \<circ> Q) (r \<circ> R)"
proof
  fix x
  show "(dual p q r \<circ> dual P Q R) x = dual (p \<circ> P) (q \<circ> Q) (r \<circ> R) x"
    by (induct x) auto
qed

lemma dualFNot': "dual invSign invSign invSign = FNot"
proof
  fix x
  show "dual invSign invSign invSign x = FNot x"
    by (induct x) auto
qed

lemma dualFNot: "dual invSign id id (FNot A) = FNot (dual invSign id id A)"
  by(induct A) (auto simp: id_def)

lemma dualId: "dual id id id A = A"
  by(induct A) (auto simp: id_def)


subsection "Frees"

primrec freeVarsF  :: "formula \<Rightarrow> vbl set"
  where
    freeVarsFAtom: "freeVarsF (FAtom z P vs)  = set vs"
  | freeVarsFConj: "freeVarsF (FConj z A0 A1) = (freeVarsF A0) \<union> (freeVarsF A1)"    
  | freeVarsFAll:  "freeVarsF (FAll  z body)  = preImage nextX (freeVarsF body)"

definition
  freeVarsFL :: "formula list \<Rightarrow> vbl set" where
  "freeVarsFL \<Gamma> = Union (freeVarsF ` (set \<Gamma>))"

lemma freeVarsF_FNot[simp]: "freeVarsF (FNot A) = freeVarsF A"
  by(induct A) auto

lemma finite_freeVarsF[simp]: "finite (freeVarsF A)"
  by(induct A) (auto simp add: inj_nextX) 

lemma freeVarsFL_nil[simp]: "freeVarsFL ([]) = {}"
  by(simp add: freeVarsFL_def)

lemma freeVarsFL_cons: "freeVarsFL (A#\<Gamma>) = freeVarsF A \<union> freeVarsFL \<Gamma>"
  by(simp add: freeVarsFL_def)

lemma finite_freeVarsFL[simp]: "finite (freeVarsFL \<Gamma>)"
  by(induct \<Gamma>) (auto simp: freeVarsFL_cons)

lemma freeVarsDual: "freeVarsF (dual p q r A) = freeVarsF A"
  by(induct A) auto


subsection "Substitutions"

primrec subF :: "[vbl \<Rightarrow> vbl,formula] \<Rightarrow> formula"
  where
    subFAtom: "subF theta (FAtom z P vs)  = FAtom z P (map theta vs)"
  | subFConj: "subF theta (FConj z A0 A1) = FConj z (subF theta A0) (subF theta A1)"
  | subFAll: "subF theta (FAll z body) = 
      FAll z (subF (\<lambda>v . (case v of zeroX \<Rightarrow> zeroX | nextX v \<Rightarrow> nextX (theta v))) body)"

lemma size_subF: "size (subF theta A) = size (A::formula)"
  by(induct A arbitrary: theta) auto

lemma subFNot: "subF theta (FNot A) = FNot (subF theta A)"
  by(induct A arbitrary: theta) auto

lemma subFDual: "subF theta (dual p q r A) = dual p q r (subF theta A)"
  by(induct A arbitrary: theta) auto

definition
  instanceF :: "[vbl,formula] \<Rightarrow> formula" where
  "instanceF w body = subF (\<lambda>v. case v of zeroX \<Rightarrow> w | nextX v \<Rightarrow> v) body"

lemma size_instance: "size (instanceF v A) = size A"
  by (simp add: instanceF_def size_subF)

lemma instanceFDual: "instanceF u (dual p q r A) = dual p q r (instanceF u A)" 
  by(induct A) (simp_all add: instanceF_def subFDual)


subsection "Models"

typedecl
  object

axiomatization obj :: "nat \<Rightarrow> object"
  where inj_obj: "inj obj"


subsection "model, non empty set and positive atom valuation"

definition "model = {z :: (object set * ([predicate,object list] \<Rightarrow> bool)). (fst z \<noteq> {})}"

typedef model = model
  unfolding model_def by auto

definition
  objects :: "model \<Rightarrow> object set" where
  "objects M = fst (Rep_model M)"

definition
  evalP :: "model \<Rightarrow> predicate \<Rightarrow> object list \<Rightarrow> bool" where
  "evalP M = snd (Rep_model M)"

lemma objectsNonEmpty: "objects M \<noteq> {}"
  using Rep_model[of M]
  by(simp add: objects_def model_def)

lemma modelsNonEmptyI: "fst (Rep_model M) \<noteq> {}"
  using Rep_model[of M] by(simp add: objects_def model_def)


subsection "Validity"

primrec evalF :: "[model,vbl \<Rightarrow> object,formula] \<Rightarrow> bool"
  where
    evalFAtom: "evalF M \<phi> (FAtom z P vs)  = sign z (evalP M P (map \<phi> vs))"
  | evalFConj: "evalF M \<phi> (FConj z A0 A1) = sign z (sign z (evalF M \<phi> A0) \<and> sign z (evalF M \<phi> A1))"
  | evalFAll:  "evalF M \<phi> (FAll  z body)  = 
      sign z (\<forall>x\<in>objects M. sign z (evalF M (\<lambda>v . (case v of zeroX   \<Rightarrow> x | nextX v \<Rightarrow> \<phi> v)) body))"

definition
  valid :: "formula \<Rightarrow> bool" where
  "valid F \<equiv> (\<forall>M \<phi>. evalF M \<phi> F = True)"


lemma evalF_FAll: "evalF M \<phi> (FAll Pos A) = (\<forall>x\<in>objects M. (evalF M (vblcase x \<phi>) A))"
  by simp
  
lemma evalF_FEx: "evalF M \<phi> (FAll Neg A) = (\<exists>x\<in>objects M. (evalF M (vblcase x \<phi>) A))"
  by simp

lemma evalF_arg2_cong: "x = y \<Longrightarrow> evalF M p x = evalF M p y" 
  by simp

lemma evalF_FNot: "!!\<phi>. evalF M \<phi> (FNot A) = (\<not> evalF M \<phi> A)"
  by(induct A rule: formula_signs_induct) simp_all

lemma evalF_equiv:  "equalOn (freeVarsF A) f g \<Longrightarrow> evalF M f A = evalF M g A"
proof(induction A arbitrary: f g)
  case (FAtom x1 x2 x3)
  then show ?case
    unfolding equalOn_def
    by (metis (mono_tags, lifting) evalFAtom freeVarsFAtom map_eq_conv)
next
  case (FConj x1 A1 A2)
  then show ?case
    by (smt (verit, ccfv_SIG) FConj equalOn_UnD evalFConj freeVarsFConj)
next
  case (FAll x1 A)
  then show ?case
    by (metis (full_types) equalOn_vblcaseI' evalF_FAll evalF_FEx freeVarsFAll
        signs.exhaust)
qed

    \<comment> \<open>composition of substitutions\<close>
lemma evalF_subF_eq: "evalF M \<phi> (subF theta A) = evalF M (\<phi> \<circ> theta) A"
proof (induction A arbitrary: \<phi> theta)
  case (FAtom x1 x2 x3)
  then show ?case
    by (metis evalFAtom list.map_comp subFAtom)
next
  case (FConj x1 A1 A2)
  then show ?case
    by auto
next
  case (FAll x1 A)
  then have "(vblcase x \<phi> \<circ> vblcase zeroX (\<lambda>v. nextX (theta v))) = (vblcase x (\<phi> \<circ> theta))"
    if "x \<in> objects M" for x
    using that 
    apply (clarsimp simp add: o_def fun_eq_iff split: vbl.splits)
    by (metis vbl_cases vblcase_nextX vblcase_zeroX)
  with FAll show ?case
    by (simp add: comp_def)
qed

lemma evalF_instance: "evalF M \<phi> (instanceF u A) = evalF M (vblcase (\<phi> u) \<phi>) A"
  by (metis comp_id comp_vblcase evalF_subF_eq fun.map_ident instanceF_def)

lemma instanceF_E: "instanceF g formula \<noteq> FAll signs formula"
  by (metis less_irrefl_nat size_instance sizelemmas(3))

end
