header "Formula"

theory Formula = Base:


subsection "Variables"

datatype vbl = X nat
  -- "FIXME there's a lot of stuff about this datatype that is
  really just a lifting from nat (what else could it be). Makes me
  wonder whether things wouldn't be clearer is we just identified vbls
  with nats"

consts deX     :: "vbl => nat"
primrec "deX (X n) = n"

lemma X_deX[simp]: "X (deX a) = a"
  apply(cases a) apply simp done

constdefs
  zeroX   :: "vbl"
  "zeroX \<equiv> X 0"

consts nextX   :: "vbl => vbl"
primrec "nextX (X n) = X (Suc n)"

constdefs vblcase :: "['a,vbl => 'a,vbl] => 'a"
  "vblcase a f n \<equiv> @z. (n=zeroX \<longrightarrow> z=a) \<and> (!x. n=nextX x \<longrightarrow> z=f(x))"

translations
  "case p of zeroX \<Rightarrow> a | nextX y \<Rightarrow> b" == "(vblcase a (%y. b) p)"
				    
constdefs freshVar :: "vbl set => vbl"
  "freshVar vs \<equiv> X (LEAST n. n \<notin> deX ` vs)"
    
lemma nextX_nextX[iff]: "nextX x = nextX y = (x =  y)"
  by(case_tac x, case_tac y, auto)

lemma inj_nextX: "inj nextX"
  by(auto simp add: inj_on_def)

lemma ind': "P zeroX ==> (! v . P v --> P (nextX v)) ==> P v'"
  apply (case_tac v', simp)
  apply(induct_tac nat)
   apply(simp add: zeroX_def)
  apply (drule_tac x="X n" in spec, simp)
  done

lemma ind: "\<lbrakk> P zeroX; \<And> v. P v \<Longrightarrow> P (nextX v) \<rbrakk> \<Longrightarrow> P v'"
  apply(rule ind') by auto

lemma zeroX_nextX[iff]: "zeroX ~= nextX a" -- "FIXME iff?"
  apply(case_tac a)
  apply(simp add: zeroX_def)
  done

lemmas nextX_zeroX[iff] = not_sym[OF zeroX_nextX]

lemma nextX: "nextX (X n) = X (Suc n)"
  apply simp done

lemma vblcase_zeroX[simp]: "vblcase a b zeroX = a" 
  by(simp add: vblcase_def)

lemma vblcase_nextX[simp]: "vblcase a b (nextX n) = b n" 
  by(simp add: vblcase_def)

lemma vbl_cases: "x = zeroX | (? y . x = nextX y)"
  apply(case_tac x, rename_tac m)
  apply(case_tac m)
  apply(simp add: zeroX_def)
  apply(rule disjI2)
  apply (rule_tac x="X nat" in exI, simp)
  done

lemma vbl_casesE: "\<lbrakk> x = zeroX \<Longrightarrow> P; \<And> y. x = nextX y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply(auto intro: vbl_cases[elim_format]) done

lemma comp_vblcase: "f o vblcase a b = vblcase (f a) (f o b)"
  apply(rule ext) 
  apply(rule_tac x = x in vbl_casesE) 
   apply(simp_all add: vblcase_zeroX vblcase_nextX) 
  done

lemma equalOn_vblcaseI': "equalOn (preImage nextX A) f g ==> equalOn A (vblcase x f) (vblcase x g)"
  apply(simp add: equalOn_def) 
  apply(rule+)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  apply(drule_tac x=y in bspec)
  apply(simp add: preImage_def) 
  by assumption
    
lemma equalOn_vblcaseI: "(zeroX : A --> x=y) ==> equalOn (preImage nextX A) f g ==> equalOn A (vblcase x f) (vblcase y g)"
  apply (rule equalOnI, rule)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  apply(simp add: preImage_def equalOn_def) 
  done

lemma X_deX_connection: "X n : A = (n : (deX ` A))"
  by force

lemma finiteFreshVar: "finite A ==> freshVar A ~: A"
  apply(simp add: freshVar_def)
  apply(simp add: X_deX_connection)
  apply(rule_tac LeastI_ex)
  apply(rule_tac x="(Suc (Max (deX ` A)))" in exI)
  apply(rule natset_finite_max)
  by force

lemma freshVarI: "[| finite A; B <= A |] ==> freshVar A ~: B"
  apply(auto dest!: finiteFreshVar) done

lemma freshVarI2: "finite A ==> !x . x ~: A --> P x ==> P (freshVar A)"
  apply(auto dest!: finiteFreshVar) done

lemmas vblsimps = vblcase_zeroX vblcase_nextX zeroX_nextX
  nextX_zeroX nextX_nextX comp_vblcase


subsection "Predicates"

datatype predicate = Predicate nat

datatype signs = Pos | Neg

lemma signsE: "\<lbrakk> signs = Neg \<Longrightarrow> P; signs = Pos \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply(cases signs, auto) done

lemma expand_signs_case: "Q(signs_case vpos vneg F) = ( 
  (F = Pos --> Q (vpos)) & 
  (F = Neg --> Q (vneg)) 
 )"
  apply(induct F) by simp_all

consts sign    :: "signs \<Rightarrow> bool \<Rightarrow> bool"
primrec 
  "sign Pos x = x"
  "sign Neg x = (\<not> x)"

lemma sign_arg_cong: "x = y ==> sign z x = sign z y" by simp
    
consts invSign :: "signs \<Rightarrow> signs"
primrec 
  "invSign Pos = Neg"
  "invSign Neg = Pos"


subsection "Formulas"

datatype formula =
    FAtom signs predicate "(vbl list)"
  | FConj signs formula formula
  | FAll  signs formula  


subsection "formula signs induct, formula signs cases"

lemma formula_signs_induct: "[|
  ! p vs. P (FAtom Pos p vs);
  ! p vs. P (FAtom Neg p vs);
  !! A B  . [| P A; P B |] ==> P (FConj Pos A B);
  !! A B  . [| P A; P B |] ==> P (FConj Neg A B);
  !! A    . [| P A |] ==> P (FAll  Pos A); 
  !! A    . [| P A |] ==> P (FAll  Neg A) 
  |]
  ==> P A"
  apply(induct_tac A) 
  apply(rule signs.induct, force, force)+
  done

lemma formula_signs_cases: "!!P. 
  [| !! p vs . P (FAtom Pos p vs); 
  !! p vs . P (FAtom Neg p vs); 
  !! f1 f2  . P (FConj Pos f1 f2); 
  !! f1 f2  . P (FConj Neg f1 f2); 
  !! f1    . P (FAll  Pos f1); 
  !! f1    . P (FAll  Neg f1) |] 
  ==> P A"
  apply(induct_tac A)
  apply(rule signs.induct, force, force)+
  done

    -- "induction using nat induction, not wellfounded induction"
lemma strong_formula_induct': "!A. (! B. size B < size A --> P B) --> P A ==> ! A. size A = n --> P (A::formula)"
  by (induct_tac n rule: nat_less_induct, blast) 

lemma strong_formula_induct: "(! A. (! B. size B < size A --> P B) --> P A) ==> P (A::formula)"
 by (rule strong_formula_induct'[rule_format], blast+) 

lemma sizelemmas: "size A < size (FConj z A B)"
  "size B < size (FConj z A B)"
  "size A < size (FAll  z A)"
  by auto

lemma expand_formula_case:
  "Q(formula_case fatom fconj fall F) = ( 
  (! z P vs  . F = FAtom z P vs  --> Q (fatom z P vs)) & 
  (! z A0 A1 . F = FConj z A0 A1 --> Q (fconj z A0 A1)) & 
  (! z A     . F = FAll  z A     --> Q (fall  z A)) 
 )"
  apply(cases F) apply simp_all done

consts FNot    :: "formula => formula"
primrec 
  FNot_FAtom: "FNot (FAtom z P vs)  = FAtom (invSign z) P vs"
  FNot_FConj: "FNot (FConj z A0 A1) = FConj (invSign z) (FNot A0) (FNot A1)"    
  FNot_FAll:  "FNot (FAll  z body)  = FAll  (invSign z) (FNot body)"

consts neg  :: "signs => signs"
primrec 
    "neg Pos = Neg"
    "neg Neg = Pos"

consts 
  dual :: "[(signs => signs),(signs => signs),(signs => signs)] => formula => formula"
primrec 
  dual_FAtom: "dual p q r (FAtom z P vs)  = FAtom (p z) P vs"
  dual_FConj: "dual p q r (FConj z A0 A1) = FConj (q z) (dual p q r A0) (dual p q r A1)"
  dual_FAll:  "dual p q r (FAll  z body)  = FAll  (r z) (dual p q r body)"

lemma dualCompose: "dual p q r o dual P Q R = dual (p o P) (q o Q) (r o R)"
  apply(rule ext)
  apply (induct_tac x, auto) 
  done

lemma dualFNot': "dual invSign invSign invSign = FNot"
  apply(rule ext) 
  apply(induct_tac x) 
  by auto

lemma dualFNot: "dual invSign id id (FNot A) = FNot (dual invSign id id A)"
  apply(induct A) apply(auto simp: id_def) done

lemma dualId: "dual id id id A = A"
  apply(induct A, auto simp: id_def) done


subsection "Frees"

consts freeVarsF  :: "formula => vbl set"
primrec 
  freeVarsFAtom: "freeVarsF (FAtom z P vs)  = set vs"
  freeVarsFConj: "freeVarsF (FConj z A0 A1) = (freeVarsF A0) Un (freeVarsF A1)"    
  freeVarsFAll:  "freeVarsF (FAll  z body)  = preImage nextX (freeVarsF body)"

constdefs
  freeVarsFL :: "formula list => vbl set"
  "freeVarsFL gamma == Union (freeVarsF ` (set gamma))"

lemma freeVarsF_FNot[simp]: "freeVarsF (FNot A) = freeVarsF A"
  apply(induct A, auto) done

lemma finite_freeVarsF[simp]: "finite (freeVarsF A)"
  apply(induct A) 
  apply(auto simp add: inj_nextX finite_preImage) 
  done 

lemma freeVarsFL_nil[simp]: "freeVarsFL ([]) = {}"
  apply(simp add: freeVarsFL_def) done

lemma freeVarsFL_cons: "freeVarsFL (A#Gamma) = freeVarsF A \<union> freeVarsFL Gamma"
  by(simp add: freeVarsFL_def)
    -- "FIXME not simp, since simp stops some later lemmas because the simpset isn't confluent"

lemma finite_freeVarsFL[simp]: "finite (freeVarsFL gamma)"
  apply(induct gamma)
  apply(auto simp: freeVarsFL_cons)
  done

lemma freeVarsDual: "freeVarsF (dual p q r A) = freeVarsF A"
  apply(induct A, auto) done


subsection "Substitutions"

consts subF         :: "[vbl => vbl,formula] => formula"
primrec 
  subFAtom: "subF theta (FAtom z P vs)  = FAtom z P (map theta vs)"
  subFConj: "subF theta (FConj z A0 A1) = FConj z (subF theta A0) (subF theta A1)"
  subFAll: "subF theta (FAll z body)  = 
  FAll  z (subF (% v . (case v of zeroX => zeroX | nextX v => nextX (theta v))) body)"

lemma size_subF[rule_format]: "! theta. size (subF theta A) = size (A::formula)"
  apply(induct A, auto) done

lemma subFNot[rule_format]: "!theta. subF theta (FNot A) = FNot (subF theta A)"
  apply(induct A, auto) done

lemma subFDual[rule_format]: "!theta. subF theta (dual p q r A) = dual p q r (subF theta A)"
  by(induct A, auto)

constdefs instanceF :: "[vbl,formula] => formula"
  "instanceF w body == subF (%v. case v of zeroX => w | nextX v => v) body"

lemma size_instance: "! v. size (instanceF v A) = size (A::formula)"
  apply(induct A) apply(auto simp: instanceF_def size_subF) done

lemma instanceFDual: "instanceF u (dual p q r A) = dual p q r (instanceF u A)" 
  apply(induct A) apply(simp_all add: instanceF_def subFDual) done


subsection "Models"

typedecl
  object

arities
   object :: type (* FIXME TJR used to be term *)

consts
  obj :: "nat => object"

axioms
  inj_obj: "inj obj"


subsection "model, non empty set and positive atom valuation"

typedef model = "{ z :: (object set * ([predicate,object list] => bool)) . (fst z ~= {}) }" by auto

consts
    objects :: "model => object set"
    evalP   :: "model => predicate => object list => bool"

defs
    objects_def: "objects M == fst (Rep_model M)"
    evalP_def:   "evalP   M == snd (Rep_model M)"


lemma evalP_arg2_cong: "x = y ==> evalP M p x = evalP M p y" by simp

lemma objectsNonEmpty: "objects M \<noteq> {}"
  using Rep_model[of M]
  by(simp add: objects_def model_def)

lemma modelsNonEmptyI: "fst (Rep_model M) \<noteq> {}"
  using Rep_model[of M] by(simp add: objects_def model_def)


subsection "Validity"

consts
    evalF            :: "[model,vbl => object,formula] => bool"
    valid            :: "formula => bool"    

defs    
    valid_def:	"valid F == ! M phi. evalF M phi F = True"

primrec 
    evalFAtom: "evalF M phi (FAtom z P vs)  = sign z (evalP M P (map phi vs))"
    evalFConj: "evalF M phi (FConj z A0 A1) = sign z (sign z (evalF M phi A0) & sign z (evalF M phi A1))"
    evalFAll:  "evalF M phi (FAll  z body)  = sign z (!x: (objects M).
				                       sign z
				                            (evalF M (%v . (case v of
										zeroX   => x
									      | nextX v => phi v)) body))"

lemma evalF_FAll: "evalF M phi (FAll Pos A) = (!x: (objects M). (evalF M (vblcase x (%v .phi v)) A))"
  apply simp done
  
lemma evalF_FEx: "evalF M phi (FAll Neg A) = ( ? x:(objects M). (evalF M (vblcase x (%v. phi v)) A))"
  apply simp done

lemma evalF_arg2_cong: "x = y ==> evalF M p x = evalF M p y" by simp

lemma evalF_FNot[rule_format]: "!phi. evalF M phi (FNot A) = (\<not> evalF M phi A)"
  apply(rule_tac formula_signs_induct)
  apply(simp+)
  done

lemma evalF_equiv[rule_format]: "! f g. (equalOn (freeVarsF A) f g) \<longrightarrow> (evalF M f A = evalF M g A)"
  apply(induct A)
    apply (force simp:equalOn_def cong: map_cong, clarify) apply simp apply(drule_tac equalOn_UnD) apply force
  apply clarify apply simp apply(rule_tac f = "sign signs" in arg_cong) apply(rule ball_cong) apply rule 
  apply(rule_tac f = "sign signs" in arg_cong) apply(force intro: equalOn_vblcaseI')
  done
    -- "FIXME tricky to automate cong args convincingly?"

    -- "composition of substitutions"
lemma evalF_subF_eq: "!phi theta. evalF M phi (subF theta A) = evalF M (phi o theta) A"
  apply(induct_tac A)
    apply(simp del: o_apply)
    apply(intro allI)
    apply(rule_tac f="sign signs" in arg_cong) 
    apply(simp add: map_compose)
   apply(simp del: o_apply)
  apply(intro allI)
  apply(simp del: o_apply)
  apply(rule_tac f="sign signs" in arg_cong) 
  apply(rule ball_cong) apply rule
  apply(rule_tac f="sign signs" in arg_cong)
  apply(subgoal_tac "(vblcase x phi \<circ> vblcase zeroX (\<lambda>v. nextX (theta v))) = (vblcase x (phi \<circ> theta))")
  apply(simp del: o_apply)
  apply(rule ext)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  done

lemma o_id'[simp]: "f o (% x. x) = f"
by (fold id_def, simp)

lemma evalF_instance: "evalF M phi (instanceF u A) = evalF M (vblcase (phi u) phi) A"
  apply(simp add: instanceF_def evalF_subF_eq vblsimps)
  done

-- "FIXME move"

lemma s[simp]:" FConj signs formula1 formula2 \<noteq> formula1"
  apply(induct_tac formula1, auto) done

lemma s'[simp]:" FConj signs formula1 formula2 \<noteq> formula2" 
  apply(induct formula2, auto) done

lemma instanceF_E: "instanceF g formula \<noteq> FAll signs formula"
  apply clarify
  apply(subgoal_tac "Suc (size (instanceF g formula)) = (size (FAll signs formula))")
  apply force
  apply(simp (no_asm) only: size_instance[rule_format])
  apply simp done

end
