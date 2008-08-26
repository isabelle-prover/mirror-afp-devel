(*  ID:         $Id: NBE.thy,v 1.7 2008-08-26 13:49:09 nipkow Exp $
    Author:     Klaus Aehlig, Tobias Nipkow
    Normalization by Evaluation
*)
(*<*)
theory NBE imports Main begin

ML"Syntax.ambiguity_level := 1000000"

declare Let_def[simp]

(* still needed for termination proofs: *)
lemma [simp]: "x \<in> set vs \<Longrightarrow> size x < Suc (list_size size vs)"
by (induct vs) auto
lemma [simp]:"x \<in> set vs \<Longrightarrow> size x < Suc (size v + list_size size vs)"
by (induct vs) auto
(*>*)
section "Terms"

types vname = nat
      ml_vname = nat

typedecl cname

text{* ML terms: *}

datatype ml =
 -- "ML"
  C_ML cname ("C\<^bsub>ML\<^esub>") (* ref to compiled code *)
| V_ML ml_vname ("V\<^bsub>ML\<^esub>")
| A_ML ml "(ml list)" ("A\<^bsub>ML\<^esub>")
| Lam_ML ml ("Lam\<^bsub>ML\<^esub>")
 -- "the universal datatype"
| C\<^isub>U cname "(ml list)"
| V\<^isub>U vname "(ml list)"
| Clo ml "(ml list)" nat
 --{*ML function \emph{apply}*}
| "apply" ml ml

text{* Lambda-terms: *}

datatype tm = C cname | V vname | \<Lambda> tm | At tm tm (infix "\<bullet>" 100)
            | "term" ml   -- {*ML function \texttt{term}*}

locale Vars =
 fixes r s t:: tm
 and rs ss ts :: "tm list"
 and u v w :: ml
 and us vs ws :: "ml list"
 and nm :: cname
 and x :: vname
 and X :: ml_vname

text{* The subset of pure terms: *}

inductive pure :: "tm \<Rightarrow> bool" where
"pure(C nm)" |
"pure(V x)" |
Lam: "pure t \<Longrightarrow> pure(\<Lambda> t)" |
"pure s \<Longrightarrow> pure t \<Longrightarrow> pure(s\<bullet>t)"

declare pure.intros[simp]

text{* Closed terms w.r.t.\ ML variables:*}

fun closed_ML :: "nat \<Rightarrow> ml \<Rightarrow> bool" ("closed\<^bsub>ML\<^esub>") where
"closed\<^bsub>ML\<^esub> i (C_ML nm) = True" |
"closed\<^bsub>ML\<^esub> i (V_ML X) = (X<i)"  |
"closed\<^bsub>ML\<^esub> i (A_ML v vs) = (closed\<^bsub>ML\<^esub> i v \<and> (\<forall>v \<in> set vs. closed\<^bsub>ML\<^esub> i v))" |
"closed\<^bsub>ML\<^esub> i (Lam_ML v) = closed\<^bsub>ML\<^esub> (i+1) v" |
"closed\<^bsub>ML\<^esub> i (C\<^isub>U nm vs) = (\<forall>v \<in> set vs. closed\<^bsub>ML\<^esub> i v)" |
"closed\<^bsub>ML\<^esub> i (V\<^isub>U nm vs) = (\<forall>v \<in> set vs. closed\<^bsub>ML\<^esub> i v)" |
"closed\<^bsub>ML\<^esub> i (Clo f vs n) = (closed\<^bsub>ML\<^esub> i f \<and> (\<forall>v \<in> set vs. closed\<^bsub>ML\<^esub> i v))" |
"closed\<^bsub>ML\<^esub> i (apply v w) = (closed\<^bsub>ML\<^esub> i v \<and> closed\<^bsub>ML\<^esub> i w)"

fun closed_tm_ML :: "nat \<Rightarrow> tm \<Rightarrow> bool" ("closed\<^bsub>ML\<^esub>") where
"closed_tm_ML i (r\<bullet>s) = (closed_tm_ML i r \<and> closed_tm_ML i s)" |
"closed_tm_ML i (\<Lambda> t) = (closed_tm_ML i t)" |
"closed_tm_ML i (term v) = closed\<^bsub>ML\<^esub> i v" |
"closed_tm_ML i v = True"

subsection "Iterated Term Application"

abbreviation foldl_At (infix "\<bullet>\<bullet>" 90) where
"t \<bullet>\<bullet> ts \<equiv> foldl (op \<bullet>) t ts"

text{*Auxiliary measure function:*}
primrec depth_At :: "tm \<Rightarrow> nat"
where
  "depth_At(C nm) = 0"
| "depth_At(V x) = 0"
| "depth_At(s \<bullet> t) = depth_At s + 1"
| "depth_At(\<Lambda> t) = 0"
| "depth_At(term v) = 0"

lemma depth_At_foldl:
 "depth_At(s \<bullet>\<bullet> ts) = depth_At s + size ts"
by (induct ts arbitrary: s) simp_all

lemma foldl_At_eq_lemma: "size ts = size ts' \<Longrightarrow>
 s \<bullet>\<bullet> ts = s' \<bullet>\<bullet> ts' \<longleftrightarrow> s = s' \<and> ts = ts'"
by (induct arbitrary: s s' rule:list_induct2) simp_all

lemma foldl_At_eq_length:
 "s \<bullet>\<bullet> ts = s \<bullet>\<bullet> ts' \<Longrightarrow> length ts = length ts'"
apply(subgoal_tac "depth_At(s \<bullet>\<bullet> ts) = depth_At(s \<bullet>\<bullet> ts')")
apply(erule thin_rl)
 apply (simp add:depth_At_foldl)
apply simp
done

lemma foldl_At_eq[simp]: "s \<bullet>\<bullet> ts = s \<bullet>\<bullet> ts' \<longleftrightarrow> ts = ts'"
apply(rule)
 prefer 2 apply simp
apply(blast dest:foldl_At_eq_lemma foldl_At_eq_length)
done

subsection "Lifting and Substitution"

fun lift_ml :: "nat \<Rightarrow> ml \<Rightarrow> ml" ("lift") where
"lift i (C_ML nm) = C_ML nm" |
"lift i (V_ML X) = V_ML X" |
"lift i (A_ML v vs) = A_ML (lift i v) (map (lift i) vs)" |
"lift i (Lam_ML v) = Lam_ML (lift i v)" |
"lift i (C\<^isub>U nm vs) = C\<^isub>U nm (map (lift i) vs)" |
"lift i (V\<^isub>U x vs) = V\<^isub>U (if x < i then x else x+1) (map (lift i) vs)" |
"lift i (Clo v vs n) = Clo (lift i v) (map (lift i) vs) n" |
"lift i (apply u v) = apply (lift i u) (lift i v)"

lemmas ml_induct = lift_ml.induct[of "\<lambda>i v. P v", standard]

fun lift_tm :: "nat \<Rightarrow> tm \<Rightarrow> tm" ("lift") where
"lift i (C nm) = C nm" |
"lift i (V x) = V(if x < i then x else x+1)" |
"lift i (s\<bullet>t) = (lift i s)\<bullet>(lift i t)" |
"lift i (\<Lambda> t) = \<Lambda>(lift (i+1) t)" |
"lift i (term v) = term (lift i v)"

fun lift_ML :: "nat \<Rightarrow> ml \<Rightarrow> ml" ("lift\<^bsub>ML\<^esub>") where
"lift\<^bsub>ML\<^esub> i (C_ML nm) = C_ML nm" |
"lift\<^bsub>ML\<^esub> i (V_ML X) = V_ML (if X < i then X else X+1)" |
"lift\<^bsub>ML\<^esub> i (A_ML v vs) = A_ML (lift\<^bsub>ML\<^esub> i v) (map (lift\<^bsub>ML\<^esub> i) vs)" |
"lift\<^bsub>ML\<^esub> i (Lam_ML v) = Lam_ML (lift\<^bsub>ML\<^esub> (i+1) v)" |
"lift\<^bsub>ML\<^esub> i (C\<^isub>U nm vs) = C\<^isub>U nm (map (lift\<^bsub>ML\<^esub> i) vs)" |
"lift\<^bsub>ML\<^esub> i (V\<^isub>U x vs) = V\<^isub>U x (map (lift\<^bsub>ML\<^esub> i) vs)" |
"lift\<^bsub>ML\<^esub> i (Clo v vs n) = Clo (lift\<^bsub>ML\<^esub> i v) (map (lift\<^bsub>ML\<^esub> i) vs) n" |
"lift\<^bsub>ML\<^esub> i (apply u v) = apply (lift\<^bsub>ML\<^esub> i u) (lift\<^bsub>ML\<^esub> i v)"

definition
 cons :: "tm \<Rightarrow> (nat \<Rightarrow> tm) \<Rightarrow> (nat \<Rightarrow> tm)" (infix "##" 65) where
"t##\<sigma> \<equiv> \<lambda>i. case i of 0 \<Rightarrow> t | Suc j \<Rightarrow> lift 0 (\<sigma> j)"

definition
 cons_ML :: "ml \<Rightarrow> (nat \<Rightarrow> ml) \<Rightarrow> (nat \<Rightarrow> ml)" (infix "##" 65) where
"v##\<sigma> \<equiv> \<lambda>i. case i of 0 \<Rightarrow> v::ml | Suc j \<Rightarrow> lift\<^bsub>ML\<^esub> 0 (\<sigma> j)"

text{* Only for pure terms! *}
primrec subst :: "(nat \<Rightarrow> tm) \<Rightarrow> tm \<Rightarrow> tm"
where
  "subst \<sigma> (C nm) = C nm"
| "subst \<sigma> (V x) = \<sigma> x"
| "subst \<sigma> (\<Lambda> t) = \<Lambda>(subst (V 0 ## \<sigma>) t)"
| "subst \<sigma> (s\<bullet>t) = (subst \<sigma> s) \<bullet> (subst \<sigma> t)"

fun subst_ML :: "(nat \<Rightarrow> ml) \<Rightarrow> ml \<Rightarrow> ml" ("subst\<^bsub>ML\<^esub>") where
"subst\<^bsub>ML\<^esub> \<sigma> (C_ML nm) = C_ML nm" |
"subst\<^bsub>ML\<^esub> \<sigma> (V_ML X) = \<sigma> X" |
"subst\<^bsub>ML\<^esub> \<sigma> (A_ML v vs) = A_ML (subst\<^bsub>ML\<^esub> \<sigma> v) (map (subst\<^bsub>ML\<^esub> \<sigma>) vs)" |
"subst\<^bsub>ML\<^esub> \<sigma> (Lam_ML v) = Lam_ML (subst\<^bsub>ML\<^esub> (V_ML 0 ## \<sigma>) v)" |
"subst\<^bsub>ML\<^esub> \<sigma> (C\<^isub>U nm vs) = C\<^isub>U nm (map (subst\<^bsub>ML\<^esub> \<sigma>) vs)" |
"subst\<^bsub>ML\<^esub> \<sigma> (V\<^isub>U x vs) = V\<^isub>U x (map (subst\<^bsub>ML\<^esub> \<sigma>) vs)" |
"subst\<^bsub>ML\<^esub> \<sigma> (Clo v vs n) = Clo (subst\<^bsub>ML\<^esub> \<sigma> v) (map (subst\<^bsub>ML\<^esub> \<sigma>) vs) n" |
"subst\<^bsub>ML\<^esub> \<sigma> (apply u v) = apply (subst\<^bsub>ML\<^esub> \<sigma> u) (subst\<^bsub>ML\<^esub> \<sigma> v)"
(* FIXME currrently needed for code generator
lemmas [code] = lift_tm.simps lift_ml.simps
lemmas [code] = subst_ML.simps *)

abbreviation
  subst_decr :: "nat \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm" where
 "subst_decr k t \<equiv> \<lambda>n. if n<k then V n else if n=k then t else V(n - 1)"
abbreviation
  subst_decr_ML :: "nat \<Rightarrow> ml \<Rightarrow> nat \<Rightarrow> ml" where
 "subst_decr_ML k v \<equiv> \<lambda>n. if n<k then V_ML n else if n=k then v else V_ML(n - 1)"
abbreviation
  subst1 :: "tm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm" ("(_/[_'/_])" [300, 0, 0] 300) where
 "s[t/k] \<equiv> subst (subst_decr k t) s"
abbreviation
  subst1_ML :: "ml \<Rightarrow> ml \<Rightarrow> nat \<Rightarrow> ml" ("(_/[_'/_])" [300, 0, 0] 300) where
 "u[v/k] \<equiv> subst\<^bsub>ML\<^esub> (subst_decr_ML k v) u"

lemma lift_foldl_At[simp]:
  "lift k (s \<bullet>\<bullet> ts) = (lift k s) \<bullet>\<bullet> (map (lift k) ts)"
by(induct ts arbitrary:s) simp_all

lemma lift_lift_ml: includes Vars shows
  "i < k+1 \<Longrightarrow> lift (Suc k) (lift i v) = lift i (lift k v)"
by(induct i v rule:lift_ml.induct)
  (simp_all add:map_compose[symmetric])
lemma lift_lift_tm: includes Vars shows
    "i < k+1 \<Longrightarrow> lift (Suc k) (lift i t) = lift i (lift k t)"
by(induct t arbitrary: i rule:lift_tm.induct)(simp_all add:lift_lift_ml)

lemma lift_lift_ML: includes Vars shows
  "i < k+1 \<Longrightarrow> lift\<^bsub>ML\<^esub> (Suc k) (lift\<^bsub>ML\<^esub> i v) = lift\<^bsub>ML\<^esub> i (lift\<^bsub>ML\<^esub> k v)"
by(induct v arbitrary: i rule:lift_ML.induct)
  (simp_all add:map_compose[symmetric])

lemma lift_lift_ML_comm: includes Vars shows
  "lift j (lift\<^bsub>ML\<^esub> i v) = lift\<^bsub>ML\<^esub> i (lift j v)"
by(induct v arbitrary: i j rule:lift_ML.induct)
  (simp_all add:map_compose[symmetric])

lemma V_ML_cons_ML_subst_decr[simp]:
  "V_ML 0 ## subst_decr_ML k v = subst_decr_ML (Suc k) (lift\<^bsub>ML\<^esub> 0 v)"
by(rule ext)(simp add:cons_ML_def split:nat.split)

lemma shift_subst_decr[simp]:
 "V 0 ## subst_decr k t = subst_decr (Suc k) (lift 0 t)"
apply(rule ext)
apply(simp add:cons_def split:nat.split)
done

lemma lift_comp_subst_decr[simp]:
  "lift 0 o subst_decr_ML k v = subst_decr_ML k (lift 0 v)"
apply(rule ext)
apply(simp add:cons_ML_def split:nat.split)
done

lemma subst_ML_ext: "\<forall>i. \<sigma> i = \<sigma>' i \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma> v = subst\<^bsub>ML\<^esub> \<sigma>' v"
by(metis ext)

lemma subst_ext: "\<forall>i. \<sigma> i = \<sigma>' i \<Longrightarrow> subst \<sigma> v = subst \<sigma>' v"
by(metis ext)

lemma lift_Pure_tms[simp]: "pure t \<Longrightarrow> pure(lift k t)"
by(induct arbitrary:k pred:pure) simp_all

lemma cons_ML_V_ML[simp]: "(V\<^bsub>ML\<^esub> 0 ## V\<^bsub>ML\<^esub>) = V_ML"
apply(rule ext)
apply(simp add:cons_ML_def split:nat.split)
done

lemma cons_V[simp]: "(V 0 ## V) = V"
apply(rule ext)
apply(simp add:cons_def split:nat.split)
done

lemma lift_o_shift: "lift k \<circ> (V_ML 0 ## \<sigma>) = (V_ML 0 ## (lift k \<circ> \<sigma>))"
apply(rule ext)
apply (simp add:cons_ML_def lift_lift_ML_comm split:nat.split)
done

lemma lift_subst_ML:
 "lift k (subst\<^bsub>ML\<^esub> \<sigma> v) = subst\<^bsub>ML\<^esub> (lift k \<circ> \<sigma>) (lift k v)"
apply(induct \<sigma> v rule:subst_ML.induct)
apply(simp_all add:map_compose[symmetric] o_assoc lift_o_shift)
apply(simp add:o_def)
done

corollary lift_subst_ML1:
  "\<forall>v k. lift_ml 0 (u[v/k]) = (lift_ml 0 u)[lift 0 v/k]"
apply(induct u rule:ml_induct)
apply(simp_all add:lift_lift_ml map_compose[symmetric] lift_subst_ML)
apply(subst lift_lift_ML_comm)apply simp
done

lemma lift_ML_subst_ML: includes Vars shows
 "lift\<^bsub>ML\<^esub> k (subst\<^bsub>ML\<^esub> \<sigma> v) =
  subst\<^bsub>ML\<^esub> (\<lambda>i. if i<k then lift\<^bsub>ML\<^esub> k (\<sigma> i) else if i=k then V_ML k else lift\<^bsub>ML\<^esub> k (\<sigma>(i - 1))) (lift\<^bsub>ML\<^esub> k v)"
  (is "_ = subst\<^bsub>ML\<^esub> (?insrt k \<sigma>) (lift\<^bsub>ML\<^esub> k v)")
apply (induct k v arbitrary: \<sigma> k rule: lift_ML.induct)
apply (simp_all add:map_compose[symmetric] o_assoc lift_o_shift)
apply(subgoal_tac "V_ML 0 ## ?insrt k \<sigma> = ?insrt (Suc k) (V_ML 0 ## \<sigma>)")
 apply simp
apply (simp add:expand_fun_eq lift_lift_ML cons_ML_def split:nat.split)
done

corollary subst_cons_lift: includes Vars shows
 "subst\<^bsub>ML\<^esub> (V_ML 0 ## \<sigma>) o (lift\<^bsub>ML\<^esub> 0) = lift\<^bsub>ML\<^esub> 0 o (subst\<^bsub>ML\<^esub> \<sigma>)"
apply(rule ext)
apply(simp add: cons_ML_def lift_ML_subst_ML)
apply(subgoal_tac "nat_case (V_ML 0) (\<lambda>j. lift\<^bsub>ML\<^esub> 0 (\<sigma> j)) = (\<lambda>i. if i = 0 then V_ML 0 else lift\<^bsub>ML\<^esub> 0 (\<sigma> (i - 1)))")
 apply simp
apply(rule ext, simp split:nat.split)
done

lemma lift_ML_id[simp]: includes Vars shows "closed\<^bsub>ML\<^esub> k v \<Longrightarrow> lift\<^bsub>ML\<^esub> k v = v"
by(induct k v rule: lift_ML.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_ML_id: includes Vars shows
  "closed\<^bsub>ML\<^esub> k v \<Longrightarrow> \<forall>i<k. \<sigma> i = V_ML i \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma> v = v"
apply (induct \<sigma> v arbitrary: k rule: subst_ML.induct)
apply (auto simp add: list_eq_iff_nth_eq)
    apply(simp add:Ball_def)
    apply(erule_tac x="vs!i" in meta_allE)
    apply(erule_tac x="k" in meta_allE)
    apply(erule_tac x="k" in meta_allE)
    apply simp
   apply(erule_tac x="Suc k" in meta_allE)
   apply (simp add:cons_ML_def split:nat.split)
   apply(erule_tac x="vs!i" in meta_allE)
   apply(erule_tac x="k" in meta_allE)
   apply simp
  apply(erule_tac x="vs!i" in meta_allE)
  apply(erule_tac x="k" in meta_allE)
  apply simp
apply(erule_tac x="vs!i" in meta_allE)
apply(erule_tac x="k" in meta_allE)
apply(erule_tac x="k" in meta_allE)
apply simp
done

corollary subst_ML_id2[simp]: "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma> v = v"
using subst_ML_id[where k=0] by simp

lemma subst_ML_coincidence:
  "closed\<^bsub>ML\<^esub> k v \<Longrightarrow> \<forall>i<k. \<sigma> i = \<sigma>' i \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma> v = subst\<^bsub>ML\<^esub> \<sigma>' v"
by (induct \<sigma> v arbitrary: k \<sigma>' rule: subst_ML.induct)
   (auto simp:cons_ML_def split:nat.split)

lemma subst_ML_comp: includes Vars shows
  "subst\<^bsub>ML\<^esub> \<sigma> (subst\<^bsub>ML\<^esub> \<sigma>' v) = subst\<^bsub>ML\<^esub> (subst\<^bsub>ML\<^esub> \<sigma>  \<circ> \<sigma>') v"
apply (induct \<sigma>' v arbitrary: \<sigma> rule: subst_ML.induct)
apply (simp_all add: list_eq_iff_nth_eq)
apply(rule subst_ML_ext)
apply(auto simp:cons_ML_def split:nat.split)
apply (metis cons_ML_def o_apply subst_cons_lift)
done

lemma subst_ML_comp2: includes Vars shows
  "\<forall>i. \<sigma>'' i = subst\<^bsub>ML\<^esub> \<sigma> (\<sigma>' i) \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma> (subst\<^bsub>ML\<^esub> \<sigma>' v) = subst\<^bsub>ML\<^esub> \<sigma>'' v"
by(simp add:subst_ML_comp subst_ML_ext)

lemma closed_tm_ML_foldl_At: includes Vars shows
  "closed\<^bsub>ML\<^esub> k (t \<bullet>\<bullet> ts) \<longleftrightarrow> closed\<^bsub>ML\<^esub> k t \<and> (\<forall>t \<in> set ts. closed\<^bsub>ML\<^esub> k t)"
by(induct ts arbitrary: t) simp_all

lemma closed_ML_lift[simp]:
  includes Vars shows "closed\<^bsub>ML\<^esub> k v \<Longrightarrow> closed\<^bsub>ML\<^esub> k (lift m v)"
by(induct k v arbitrary: m rule: lift_ML.induct)
  (simp_all add:list_eq_iff_nth_eq)

lemma closed_ML_Suc: "closed\<^bsub>ML\<^esub> n v \<Longrightarrow> closed\<^bsub>ML\<^esub> (Suc n) (lift\<^bsub>ML\<^esub> k v)"
by (induct k v arbitrary: n rule: lift_ML.induct) simp_all

lemma closed_ML_subst_ML:
  "\<forall>i. closed\<^bsub>ML\<^esub> k (\<sigma> i) \<Longrightarrow> closed\<^bsub>ML\<^esub> k (subst\<^bsub>ML\<^esub> \<sigma> v)"
by(induct \<sigma> v arbitrary: k rule: subst_ML.induct)
  (auto simp:cons_ML_def closed_ML_Suc split:nat.split)

lemma closed_ML_subst_ML2:
  "closed\<^bsub>ML\<^esub> k v \<Longrightarrow> \<forall>i<k. closed\<^bsub>ML\<^esub> l (\<sigma> i) \<Longrightarrow> closed\<^bsub>ML\<^esub> l (subst\<^bsub>ML\<^esub> \<sigma> v)"
by(induct \<sigma> v arbitrary: k l rule: subst_ML.induct)
  (auto simp:cons_ML_def closed_ML_Suc split:nat.split)


lemma subst_foldl[simp]:
 "subst \<sigma> (s \<bullet>\<bullet> ts) = (subst \<sigma> s) \<bullet>\<bullet> (map (subst \<sigma>) ts)"
by (induct ts arbitrary: s) auto

lemma subst_V: "pure t \<Longrightarrow> subst V t = t"
by(induct pred:pure) simp_all

lemma lift_subst_aux:
  "pure t \<Longrightarrow> \<forall>i<k. \<sigma>' i = lift k (\<sigma> i) \<Longrightarrow>
   \<forall>i\<ge>k. \<sigma>'(Suc i) = lift k (\<sigma> i) \<Longrightarrow> 
  \<sigma>' k = V k \<Longrightarrow> lift k (subst \<sigma> t) = subst \<sigma>' (lift k t)"
apply(induct arbitrary:\<sigma> \<sigma>' k pred:pure)
apply (simp_all add: split:nat.split)
apply(erule meta_allE)+
apply(erule meta_impE)
defer
apply(erule meta_impE)
defer
apply(erule meta_mp)
apply (simp_all add: cons_def lift_lift_ml lift_lift_tm split:nat.split)
done

corollary lift_subst:
  "pure t \<Longrightarrow> lift 0 (subst \<sigma> t) = subst (V 0 ## \<sigma>) (lift 0 t)"
by (simp add: lift_subst_aux cons_def lift_lift_ml split:nat.split)

lemma subst_comp: includes Vars shows
  "pure t \<Longrightarrow> \<forall>i. pure(\<sigma>' i) \<Longrightarrow>
   \<sigma>'' = (\<lambda>i. subst \<sigma> (\<sigma>' i)) \<Longrightarrow> subst \<sigma> (subst \<sigma>' t) = subst \<sigma>'' t"
apply(induct arbitrary:\<sigma> \<sigma>' \<sigma>'' pred:pure)
apply simp
apply simp
defer
apply simp
apply (simp (no_asm))
apply(erule meta_allE)+
apply(erule meta_impE)
defer
apply(erule meta_mp)
prefer 2 apply (simp add:cons_def split:nat.split)
apply(rule ext)
apply(subst (1) cons_def)
apply(subst (2) cons_def)
apply(simp split:nat.split)
apply rule apply (simp add:cons_def)
apply(simp add:lift_subst)
done


section "Reduction"

text{* Rewrite rules and their compiled version: *}
axiomatization
  R :: "(cname * tm list * tm)set"
consts
  compR :: "(cname * ml list * ml)set"

text{* Reduction of lambda-terms: *}

inductive_set
  tRed :: "(tm * tm)set"
  and tred :: "[tm, tm] => bool"  (infixl "\<rightarrow>" 50)
where
  "s \<rightarrow> t \<equiv> (s, t) \<in> tRed"
 -- {*$\beta$-reduction*}
| "(\<Lambda> t) \<bullet> s \<rightarrow> t[s/0]"
 -- {*$\eta$-expansion*}
| "t \<rightarrow> \<Lambda> ((lift 0 t) \<bullet> (V 0))"
 -- "Rewriting"
| "(nm,ts,t) : R \<Longrightarrow> (C nm) \<bullet>\<bullet> (map (subst \<sigma>) ts) \<rightarrow> subst \<sigma> t"
| "t \<rightarrow> t' \<Longrightarrow> \<Lambda> t \<rightarrow> \<Lambda> t'"
| "s \<rightarrow> s' \<Longrightarrow> s \<bullet> t \<rightarrow> s' \<bullet> t"
| "t \<rightarrow> t' \<Longrightarrow> s \<bullet> t \<rightarrow> s \<bullet> t'"

abbreviation
  treds :: "[tm, tm] => bool"  (infixl "\<rightarrow>*" 50) where
  "s \<rightarrow>* t \<equiv> (s, t) \<in> tRed^*"

inductive_set
  tRed_list :: "(tm list * tm list) set"
  and treds_list :: "[tm list, tm list] \<Rightarrow> bool" (infixl "\<rightarrow>*" 50)
where
  "ss \<rightarrow>* ts \<equiv> (ss, ts) \<in> tRed_list"
| "[] \<rightarrow>* []"
| "ts \<rightarrow>* ts' \<Longrightarrow> t \<rightarrow>* t' \<Longrightarrow> t#ts \<rightarrow>* t'#ts'"

text{* Reduction of ML-terms: *}

declare conj_cong[fundef_cong]

function no_match_ML ("no'_match\<^bsub>ML\<^esub>") where
"no_match_ML ps os = (\<exists>i < min (size os) (size ps).
   \<exists>nm nm' vs vs'. ps!i = C\<^isub>U nm vs \<and> os!i = C\<^isub>U nm' vs' \<and>
      (nm=nm' \<longrightarrow> no_match_ML vs vs'))"
by pat_completeness auto
termination
apply(relation "measure(%(vs::ml list,_). \<Sum>v\<leftarrow>vs. size v)")
apply auto
sorry

abbreviation
"no_match_compR nm os == (\<forall>(nm',ps,v)\<in> compR. nm=nm' \<longrightarrow> no_match_ML ps os)"

declare no_match_ML.simps[simp del]

declare conj_cong[fundef_cong del]

inductive_set
  Red :: "(ml * ml)set"
  and Redl :: "(ml list * ml list)set"
  and red :: "[ml, ml] => bool"  (infixl "\<Rightarrow>" 50)
  and redl :: "[ml list, ml list] => bool"  (infixl "\<Rightarrow>" 50)
  and reds :: "[ml, ml] => bool"  (infixl "\<Rightarrow>*" 50)
where
  "s \<Rightarrow> t \<equiv> (s, t) \<in> Red"
| "s \<Rightarrow> t \<equiv> (s, t) \<in> Redl"
| "s \<Rightarrow>* t \<equiv> (s, t) \<in> Red^*"
 -- {* ML $\beta$-reduction *}
| "A_ML (Lam_ML u) [v] \<Rightarrow> u[v/0]"
 -- "Execution of a compiled rewrite rule"
| "(nm,vs,v) : compR \<Longrightarrow> \<forall> i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i) \<Longrightarrow>
   A_ML (C_ML nm) (map (subst\<^bsub>ML\<^esub> \<sigma>) vs) \<Rightarrow> subst\<^bsub>ML\<^esub> \<sigma> v"
-- {* default rule: *}
| "\<forall>i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i)
   \<Longrightarrow> vs = map V\<^bsub>ML\<^esub> [0..<arity nm] \<Longrightarrow> ls = map (subst\<^bsub>ML\<^esub> \<sigma>) vs
   \<Longrightarrow> \<forall>(nm',vs',v') \<in> compR. nm=nm' \<longrightarrow> no_match\<^bsub>ML\<^esub> vs' ls
   \<Longrightarrow> A_ML (C_ML nm) ls \<Rightarrow> subst\<^bsub>ML\<^esub> \<sigma> (C\<^isub>U nm vs)"
 -- {* Equations for function \texttt{apply}*}
| apply_Clo1: "apply (Clo f vs (Suc 0)) v \<Rightarrow> A_ML f (v # vs)"
| apply_Clo2: "n > 0 \<Longrightarrow>
 apply (Clo f vs (Suc n)) v \<Rightarrow> Clo f (v # vs) n"
| apply_C: "apply (C\<^isub>U nm vs) v \<Rightarrow> C\<^isub>U nm (v # vs)"
| apply_V: "apply (V\<^isub>U x vs) v \<Rightarrow> V\<^isub>U x (v # vs)"
 -- "Context rules"
| ctxt_C: "vs \<Rightarrow> vs' \<Longrightarrow> C\<^isub>U nm vs \<Rightarrow> C\<^isub>U nm vs'"
| ctxt_V: "vs \<Rightarrow> vs' \<Longrightarrow> V\<^isub>U x vs \<Rightarrow> V\<^isub>U x vs'"
| ctxt_Clo1: "f \<Rightarrow> f'   \<Longrightarrow> Clo f vs n \<Rightarrow> Clo f' vs n"
| ctxt_Clo3: "vs \<Rightarrow> vs' \<Longrightarrow> Clo f vs n \<Rightarrow> Clo f vs' n"
| ctxt_apply1: "s \<Rightarrow> s'   \<Longrightarrow> apply s t \<Rightarrow> apply s' t"
| ctxt_apply2: "t \<Rightarrow> t'   \<Longrightarrow> apply s t \<Rightarrow> apply s t'"
| ctxt_A_ML1: "f \<Rightarrow> f'   \<Longrightarrow> A_ML f vs \<Rightarrow> A_ML f' vs"
| ctxt_A_ML2: "vs \<Rightarrow> vs' \<Longrightarrow> A_ML f vs \<Rightarrow> A_ML f vs'"
| ctxt_list1: "v \<Rightarrow> v'   \<Longrightarrow> v#vs \<Rightarrow> v'#vs"
| ctxt_list2: "vs \<Rightarrow> vs' \<Longrightarrow> v#vs \<Rightarrow> v#vs'"

inductive_set
  Redt :: "(tm * tm)set"
  and redt :: "[tm, tm] => bool"  (infixl "\<Rightarrow>" 50)
  and redts :: "[tm, tm] => bool"  (infixl "\<Rightarrow>*" 50)
where
  "s \<Rightarrow> t \<equiv> (s, t) \<in> Redt"
| "s \<Rightarrow>* t \<equiv> (s, t) \<in> Redt^*"
 --{* function \texttt{term} *}
| term_C: "term (C\<^isub>U nm vs) \<Rightarrow> (C nm) \<bullet>\<bullet> (map term (rev vs))"
| term_V: "term (V\<^isub>U x vs) \<Rightarrow> (V x) \<bullet>\<bullet> (map term (rev vs))"
| term_Clo: "term(Clo vf vs n) \<Rightarrow> \<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^isub>U 0 [])))"
 -- "context rules"
| ctxt_Lam: "t \<Rightarrow> t' \<Longrightarrow> \<Lambda> t \<Rightarrow> \<Lambda> t'"
| ctxt_At1: "s \<Rightarrow> s' \<Longrightarrow> s \<bullet> t \<Rightarrow> s' \<bullet> t"
| ctxt_At2: "t \<Rightarrow> t' \<Longrightarrow> s \<bullet> t \<Rightarrow> s \<bullet> t'"
| ctxt_term: "v \<Rightarrow> v' \<Longrightarrow> term v \<Rightarrow> term v'"

declare tRed_list.intros[simp]

lemma tRed_list_refl[simp]: includes Vars shows "ts \<rightarrow>* ts"
by(induct ts) auto

lemma tRed_append: "rs \<rightarrow>* rs' \<Longrightarrow> ts \<rightarrow>* ts' \<Longrightarrow> rs @ ts \<rightarrow>* rs' @ ts'"
by(induct set: tRed_list) auto

lemma tRed_rev: "ts \<rightarrow>* ts' \<Longrightarrow> rev ts \<rightarrow>* rev ts'"
by(induct set: tRed_list) (auto simp:tRed_append)

lemma red_Lam[simp]: includes Vars shows "t \<rightarrow>* t' \<Longrightarrow> \<Lambda> t \<rightarrow>* \<Lambda> t'"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro: rtrancl_into_rtrancl tRed.intros)
done

lemma red_At1[simp]: includes Vars shows "t \<rightarrow>* t' \<Longrightarrow> t \<bullet> s \<rightarrow>* t' \<bullet> s"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro: rtrancl_into_rtrancl tRed.intros)
done

lemma red_At2[simp]: includes Vars shows "t \<rightarrow>* t' \<Longrightarrow> s \<bullet> t \<rightarrow>* s \<bullet> t'"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro:rtrancl_into_rtrancl tRed.intros)
done

lemma tRed_list_foldl_At:
 "ts \<rightarrow>* ts' \<Longrightarrow> s \<rightarrow>* s' \<Longrightarrow> s \<bullet>\<bullet> ts \<rightarrow>* s' \<bullet>\<bullet> ts'"
apply(induct arbitrary:s s' rule:tRed_list.induct)
apply simp
apply simp
apply(blast dest: red_At1 red_At2 intro:rtrancl_trans)
done

section "Kernel"

text{* First a special size function and some lemmas for the
termination proof of the kernel function. *}

fun size' :: "ml \<Rightarrow> nat" where
"size' (C_ML nm) = 1" |
"size' (V_ML X) = 1"  |
"size' (A_ML v vs) = (size' v + (\<Sum>v\<leftarrow>vs. size' v))+1" |
"size' (Lam_ML v) = size' v + 1" |
"size' (C\<^isub>U nm vs) = (\<Sum>v\<leftarrow>vs. size' v)+1" |
"size' (V\<^isub>U nm vs) = (\<Sum>v\<leftarrow>vs. size' v)+1" |
"size' (Clo f vs n) = (size' f + (\<Sum>v\<leftarrow>vs. size' v))+1" |
"size' (apply v w) = (size' v + size' w)+1"

lemma listsum_size'[simp]:
 "v \<in> set vs \<Longrightarrow> size' v < Suc(listsum (map size' vs))"
by(induct vs)(auto)

corollary cor_listsum_size'[simp]:
 "v \<in> set vs \<Longrightarrow> size' v < Suc(m + listsum (map size' vs))"
using listsum_size'[of v vs] by arith

lemma size'_lift_ML: "size' (lift\<^bsub>ML\<^esub> k v) = size' v"
apply(induct v arbitrary:k rule:size'.induct)
apply (simp_all add:map_compose[symmetric])
   apply(rule arg_cong[where f = listsum])
   apply(rule map_ext)
   apply simp
  apply(rule arg_cong[where f = listsum])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = listsum])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = listsum])
apply(rule map_ext)
apply simp
done

lemma size'_subst_ML[simp]:
 "\<forall>i j. size'(\<sigma> i) = 1 \<Longrightarrow> size' (subst\<^bsub>ML\<^esub> \<sigma> v) = size' v"
apply(induct v arbitrary:\<sigma> rule:size'.induct)
apply (simp_all add:map_compose[symmetric])
    apply(rule arg_cong[where f = listsum])
    apply(rule map_ext)
    apply simp
   apply(erule meta_allE)
   apply(erule meta_mp)
   apply(simp add:cons_ML_def size'_lift_ML split:nat.split)
  apply(rule arg_cong[where f = listsum])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = listsum])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = listsum])
apply(rule map_ext)
apply simp
done

lemma size'_lift[simp]: "size' (lift i v) = size' v"
apply(induct v arbitrary:i rule:size'.induct)
apply (simp_all add:map_compose[symmetric])
   apply(rule arg_cong[where f = listsum])
   apply(rule map_ext)
   apply simp
  apply(rule arg_cong[where f = listsum])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = listsum])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = listsum])
apply(rule map_ext)
apply simp
done

function kernel  :: "ml \<Rightarrow> tm"  ("_!" 300) where
"(C_ML nm)! = C nm" |
"(A_ML v vs)! = v! \<bullet>\<bullet> (map kernel (rev vs))" |
"(Lam_ML v)! = \<Lambda> (((lift 0 v)[V\<^isub>U 0 []/0])!)" |
"(C\<^isub>U nm vs)! = (C nm) \<bullet>\<bullet> (map kernel (rev vs))" |
"(V\<^isub>U x vs)! = (V x) \<bullet>\<bullet> (map kernel (rev vs))" |
"(Clo f vs n)! = f! \<bullet>\<bullet> (map kernel (rev vs))" |
"(apply v w)! = v! \<bullet> (w!)" |
"(V_ML X)! = undefined"
by pat_completeness auto
termination by(relation "measure size'") auto

primrec kernelt :: "tm \<Rightarrow> tm" ("_!" 300)
where
  "(C nm)! = C nm"
| "(V x)! = V x"
| "(s \<bullet> t)! = (s!) \<bullet> (t!)"
| "(\<Lambda> t)! = \<Lambda>(t!)"
| "(term v)! = v!"

abbreviation
  kernels :: "ml list \<Rightarrow> tm list" ("_!" 300) where
  "vs! \<equiv> map kernel vs"

lemma kernel_pure: includes Vars assumes "pure t" shows "t! = t"
using assms by (induct) simp_all

lemma kernel_foldl_At[simp]: "(s \<bullet>\<bullet> ts)! = (s!) \<bullet>\<bullet> (map kernelt ts)"
by (induct ts arbitrary: s) simp_all

lemma kernelt_o_term[simp]: "(kernelt \<circ> term) = kernel"
by(rule ext) simp

lemma includes Vars shows pure_foldl:
 "pure t \<Longrightarrow> \<forall>t\<in>set ts. pure t \<Longrightarrow> 
 (!!s t. pure s \<Longrightarrow> pure t \<Longrightarrow> pure(f s t)) \<Longrightarrow>
 pure(foldl f t ts)"
by(induct ts arbitrary: t) simp_all

lemma pure_kernel: includes Vars shows "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> pure(v!)"
apply(induct v rule:kernel.induct)
apply (auto simp:pure_foldl)
apply(rule pure.intros)
apply(erule meta_mp)
apply(subgoal_tac "closed\<^bsub>ML\<^esub> (Suc 0) (lift 0 v)")
apply(subgoal_tac "closed\<^bsub>ML\<^esub> 0 (subst\<^bsub>ML\<^esub> (\<lambda>n. V\<^isub>U 0 []) (lift 0 v))")
apply(drule subst_ML_coincidence[of _ _ "\<lambda>n. V\<^isub>U 0 []" "\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - 1)"])back
apply simp
apply metis
apply simp
apply(rule closed_ML_subst_ML)
apply simp+
done

corollary subst_V_kernel: includes Vars shows
  "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> subst V (v!) = v!"
by (metis pure_kernel subst_V)

lemma kernel_lift_tm: includes Vars shows
  "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> (lift i v)! = lift i (v!)"
apply(induct v arbitrary: i rule: kernel.induct)
apply (simp_all add:list_eq_iff_nth_eq)
 apply(simp add: rev_nth)
defer
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
apply(erule_tac x="Suc i" in meta_allE)
apply(erule meta_impE)
defer
apply (simp add:lift_subst_ML)
apply(subgoal_tac "lift (Suc i) \<circ> (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - 1)) = (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - 1))")
apply (simp add:lift_lift_ml)
apply(rule ext)
apply(simp)
apply(subst closed_ML_subst_ML2[of "1"])
apply(simp)
apply(simp)
apply(simp)
done

subsection "An auxiliary substitution"

text{* This function is only introduced to prove the involved susbtitution
lemma @{text kernel_subst1} below. *}

fun subst_ml :: "(nat \<Rightarrow> nat) \<Rightarrow> ml \<Rightarrow> ml" where
"subst_ml \<sigma> (C_ML nm) = C_ML nm" |
"subst_ml \<sigma> (V_ML X) = V_ML X" |
"subst_ml \<sigma> (A_ML v vs) = A_ML (subst_ml \<sigma> v) (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (Lam_ML v) = Lam_ML (subst_ml \<sigma> v)" |
"subst_ml \<sigma> (C\<^isub>U nm vs) = C\<^isub>U nm (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (V\<^isub>U x vs) = V\<^isub>U (\<sigma> x) (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (Clo v vs n) = Clo (subst_ml \<sigma> v) (map (subst_ml \<sigma>) vs) n" |
"subst_ml \<sigma> (apply u v) = apply (subst_ml \<sigma> u) (subst_ml \<sigma> v)"

lemma lift_ML_subst_ml:
  "lift\<^bsub>ML\<^esub> k (subst_ml \<sigma> v) = subst_ml \<sigma> (lift\<^bsub>ML\<^esub> k v)"
apply (induct \<sigma> v arbitrary: k rule:subst_ml.induct)
apply (simp_all add:list_eq_iff_nth_eq)
done

lemma subst_ml_subst_ML: includes Vars shows
  "subst_ml \<sigma> (subst\<^bsub>ML\<^esub> \<sigma>' v) = subst\<^bsub>ML\<^esub> (subst_ml \<sigma> o \<sigma>') (subst_ml \<sigma> v)"
apply (induct \<sigma>' v arbitrary: \<sigma> rule: subst_ML.induct)
apply(simp_all add:list_eq_iff_nth_eq)
apply(subgoal_tac "(subst_ml \<sigma>' \<circ> V_ML 0 ## \<sigma>) = V_ML 0 ## (subst_ml \<sigma>' \<circ> \<sigma>)")
apply simp
apply(rule ext)
apply(simp add:cons_ML_def lift_ML_subst_ml split:nat.split)
done


text{* Maybe this should be the def of lift: *}
lemma lift_is_subst_ml: "lift k v = subst_ml (\<lambda>n. if n<k then n else n+1) v"
by(induct k v rule:lift_ml.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_ml_comp:  "subst_ml \<sigma> (subst_ml \<sigma>' v) = subst_ml (\<sigma> o \<sigma>') v"
by(induct \<sigma>' v rule:subst_ml.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_kernel:
  "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow>  subst (\<lambda>n. V(\<sigma> n)) (v!) = (subst_ml \<sigma> v)!"
apply (induct v arbitrary: \<sigma> rule:kernel.induct)
apply (simp_all add:list_eq_iff_nth_eq)
 apply(simp add: rev_nth)
defer
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
apply(erule_tac x="\<lambda>n. case n of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> Suc(\<sigma> k)" in meta_allE)
apply(erule_tac meta_impE)
apply(rule closed_ML_subst_ML2[where k="Suc 0"])
apply (metis closed_ML_lift)
apply simp
apply(subgoal_tac "(\<lambda>n. V(case n of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> Suc (\<sigma> k))) = (V 0 ## (\<lambda>n. V(\<sigma> n)))")
apply (simp add:subst_ml_subst_ML)
defer
apply(simp add:expand_fun_eq cons_def split:nat.split)
apply(simp add:cons_def)
defer
apply(simp add:lift_is_subst_ml subst_ml_comp)
apply(rule arg_cong[where f = kernel])
apply(subgoal_tac "(nat_case 0 (\<lambda>k. Suc (\<sigma> k)) \<circ> Suc) = Suc o \<sigma>")
prefer 2 apply(simp add:expand_fun_eq split:nat.split)
apply(subgoal_tac "(subst_ml (nat_case 0 (\<lambda>k. Suc (\<sigma> k))) \<circ>
               (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - 1)))
             = (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - 1))")
apply simp
apply(simp add: expand_fun_eq split:nat.split)
done

lemma if_cong0: "If x y z = If x y z"
by simp

lemma kernel_subst1:
  "closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> closed\<^bsub>ML\<^esub> (Suc 0) u \<Longrightarrow>
   kernel(u[v/0]) = (kernel((lift 0 u)[V\<^isub>U 0 []/0]))[v!/0]"
proof(induct u arbitrary:v rule:kernel.induct)
  case (3 w)
  show ?case (is "?L = ?R")
  proof -
    have "?L = \<Lambda>(lift 0 (w[lift\<^bsub>ML\<^esub> 0 v/Suc 0])[V\<^isub>U 0 []/0] !)"
      by (simp cong:if_cong0)
    also have "\<dots> = \<Lambda>((lift 0 w)[lift\<^bsub>ML\<^esub> 0 (lift 0 v)/Suc 0][V\<^isub>U 0 []/0]!)"
      by(simp only: lift_subst_ML1 lift_lift_ML_comm)
    also have "\<dots> = \<Lambda>(subst\<^bsub>ML\<^esub> (\<lambda>n. if n=0 then V\<^isub>U 0 [] else
            if n=Suc 0 then lift 0 v else V_ML (n - 2)) (lift 0 w) !)"
      apply simp
      apply(rule arg_cong[where f = kernel])
      apply(rule subst_ML_comp2)
      using 3
      apply auto
      done
    also have "\<dots> = \<Lambda>((lift 0 w)[V\<^isub>U 0 []/0][lift 0 v/0]!)"
      apply simp
      apply(rule arg_cong[where f = kernel])
      apply(rule subst_ML_comp2[symmetric])
      using 3
      apply auto
      done
    also have "\<dots> = \<Lambda>((lift_ml 0 ((lift_ml 0 w)[V\<^isub>U 0 []/0]))[V\<^isub>U 0 []/0]![(lift 0 v)!/0])"
      apply(rule arg_cong[where f = \<Lambda>])
      apply(rule 3(1))
      apply (metis closed_ML_lift 3(2))
      apply(subgoal_tac "closed\<^bsub>ML\<^esub> (Suc(Suc 0)) w")
      defer
      using 3
      apply force
      apply(subgoal_tac  "closed\<^bsub>ML\<^esub> (Suc (Suc 0)) (lift 0 w)")
      defer
      apply(erule closed_ML_lift)
      apply(erule closed_ML_subst_ML2)
      apply simp
      done
    also have "\<dots> = \<Lambda>((lift_ml 0 (lift_ml 0 w)[V\<^isub>U 1 []/0])[V\<^isub>U 0 []/0]![(lift 0 v)!/0])" (is "_ = ?M")
      apply(subgoal_tac "lift_ml 0 (lift_ml 0 w[V\<^isub>U 0 []/0])[V\<^isub>U 0 []/0] =
                         lift_ml 0 (lift_ml 0 w)[V\<^isub>U 1 []/0][V\<^isub>U 0 []/0]")
      apply simp
      apply(subst lift_subst_ML)
      apply(simp add:comp_def if_distrib[where f="lift_ml 0"] cong:if_cong)
      done
    finally have "?L = ?M" .
    have "?R = \<Lambda> (subst (V 0 ## subst_decr 0 (v!))
          (lift 0 (lift_ml 0 w[V\<^isub>U 0 []/Suc 0])[V\<^isub>U 0 []/0]!))"
      apply(subgoal_tac "(V_ML 0 ## (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V_ML (n - Suc 0))) = subst_decr_ML (Suc 0) (V\<^isub>U 0 [])")
      apply(simp cong:if_cong)
      apply(simp add:expand_fun_eq cons_ML_def split:nat.splits)
      done
    also have "\<dots> = \<Lambda> (subst (V 0 ## subst_decr 0 (v!))
          ((lift 0 (lift_ml 0 w))[V\<^isub>U 1 []/Suc 0][V\<^isub>U 0 []/0]!))"
      apply(subgoal_tac "lift 0 (lift 0 w[V\<^isub>U 0 []/Suc 0]) = lift 0 (lift 0 w)[V\<^isub>U 1 []/Suc 0]")
      apply simp
      apply(subst lift_subst_ML)
      apply(simp add:comp_def if_distrib[where f="lift_ml 0"] cong:if_cong)
      done
    also have "(lift_ml 0 (lift_ml 0 w))[V\<^isub>U 1 []/Suc 0][V\<^isub>U 0 []/0] =
               (lift 0 (lift_ml 0 w))[V\<^isub>U 0 []/0][V\<^isub>U 1 []/ 0]" (is "?l = ?r")
    proof -
      have "?l = subst\<^bsub>ML\<^esub> (\<lambda>n. if n= 0 then V\<^isub>U 0 [] else if n = 1 then V\<^isub>U 1 [] else
                      V_ML (n - 2))
               (lift_ml 0 (lift_ml 0 w))"
      by(auto intro!:subst_ML_comp2)
    also have "\<dots> = ?r" by(auto intro!:subst_ML_comp2[symmetric])
    finally show ?thesis .
  qed
  also have "\<Lambda> (subst (V 0 ## subst_decr 0 (v!)) (?r !)) = ?M"
  proof-
    have "subst (subst_decr (Suc 0) (lift_tm 0 (kernel v))) (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 0 []/0][V\<^isub>U 1 []/0]!) =
    subst (subst_decr 0 (kernel(lift_ml 0 v))) (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 1 []/0][V\<^isub>U 0 []/0]!)" (is "?a = ?b")
    proof-
      def pi == "\<lambda>n::nat. if n = 0 then 1 else if n = 1 then 0 else n"
      have "(\<lambda>i. V (pi i)[lift 0 (v!)/0]) = subst_decr (Suc 0) (lift 0 (v!))"
	by(rule ext)(simp add:pi_def)
      hence "?a =
  subst (subst_decr 0 (lift_tm 0 (kernel v))) (subst (\<lambda> n. V(pi n)) (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 0 []/0][V\<^isub>U 1 []/0]!))"
	apply(subst subst_comp[OF _ _ refl])
	prefer 3 apply simp
	using 3(3)
	apply simp
	apply(rule pure_kernel)
	apply(rule closed_ML_subst_ML2[where k="Suc 0"])
	apply(rule closed_ML_subst_ML2[where k="Suc(Suc 0)"])
	apply simp
	apply simp
	apply simp
	apply simp
	done
      also have "\<dots> =
 (subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 0 []/0][V\<^isub>U 1 []/0]))![lift_tm 0 (v!)/0]"
	apply(subst subst_kernel)
	using 3 apply auto
	apply(rule closed_ML_subst_ML2[where k="Suc 0"])
	apply(rule closed_ML_subst_ML2[where k="Suc(Suc 0)"])
	apply simp
	apply simp
	apply simp
	done
      also have "\<dots> = (subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 0 []/0][V\<^isub>U 1 []/0]))![lift 0 v!/0]"
      proof -
	have "lift 0 (v!) = lift 0 v!" by (metis 3(2) kernel_lift_tm)
	thus ?thesis by (simp cong:if_cong)
      qed
      also have "\<dots> = ?b"
      proof-
	have 1: "subst_ml pi (lift 0 (lift 0 w)) = lift 0 (lift 0 w)"
	  apply(simp add:lift_is_subst_ml subst_ml_comp)
	  apply(subgoal_tac "pi \<circ> (Suc \<circ> Suc) = (Suc \<circ> Suc)")
	  apply(simp)
	  apply(simp add:pi_def expand_fun_eq)
	  done
	have "subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^isub>U 0 []/0][V\<^isub>U 1 []/0]) =
             lift_ml 0 (lift_ml 0 w)[V\<^isub>U 1 []/0][V\<^isub>U 0 []/0]"
	  apply(subst subst_ml_subst_ML)
	  apply(subst subst_ml_subst_ML)
	  apply(subst 1)
	  apply(subst subst_ML_comp)
	  apply(rule subst_ML_comp2[symmetric])
	  apply(auto simp:pi_def)
	  done
	thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    thus ?thesis by(simp cong:if_cong0 add:shift_subst_decr)
  qed
  finally have "?R = ?M" .
  then show "?L = ?R" using `?L = ?M` by metis
qed
qed (simp_all add:list_eq_iff_nth_eq, (simp_all add:rev_nth)?)


section "Compiler"

axiomatization arity :: "cname \<Rightarrow> nat"

primrec compile :: "tm \<Rightarrow> (nat \<Rightarrow> ml) \<Rightarrow> ml"
where
  "compile (V x) \<sigma> = \<sigma> x"
| "compile (C nm) \<sigma> = Clo (C\<^bsub>ML\<^esub> nm) [] (arity nm)"
| "compile (s \<bullet> t) \<sigma> = apply (compile s \<sigma>) (compile t \<sigma>)"
| "compile (\<Lambda> t) \<sigma> = Clo (Lam\<^bsub>ML\<^esub> (compile t (V\<^bsub>ML\<^esub> 0 ## \<sigma>))) [] 1"

text{* Compiler for open terms and for terms with fixed free variables: *}

definition "comp_open t = compile t V\<^bsub>ML\<^esub>"
abbreviation "comp_fixed t \<equiv> compile t (\<lambda>i. V\<^isub>U i [])"

text{* Compiled rules: *}

defs compR_def:
 "compR \<equiv> (\<lambda>(nm,ts,t). (nm, map comp_open (rev ts), comp_open t)) ` R"

text{* Axioms about @{text R}: *}

axiomatization where
pure_R: "(nm,ts,t) : R \<Longrightarrow> (\<forall>t \<in> set ts. pure t) \<and> pure t"

lemma lift_compile:
 "pure t \<Longrightarrow> \<forall>\<sigma> k. lift k (compile t \<sigma>) = compile t (lift k \<circ> \<sigma>)"
apply(induct pred:pure)
apply simp_all
apply clarsimp
apply(rule_tac f = "compile t" in arg_cong)
apply(rule ext)
apply (clarsimp simp:cons_ML_def lift_lift_ML_comm split:nat.split)
done

lemma subst_ML_compile:
  "pure t \<Longrightarrow> subst\<^bsub>ML\<^esub> \<sigma>' (compile t \<sigma>) = compile t (subst\<^bsub>ML\<^esub> \<sigma>' o \<sigma>)"
apply(induct arbitrary: \<sigma> \<sigma>' pred:pure)
apply simp_all
apply(erule_tac x="V_ML 0 ## \<sigma>'" in meta_allE)
apply(erule_tac x= "V_ML 0 ## (lift\<^bsub>ML\<^esub> 0 \<circ> \<sigma>)" in meta_allE)
apply(rule_tac f = "compile t" in arg_cong)
apply(rule ext)
apply (auto simp add:subst_ML_ext cons_ML_def lift_ML_subst_ML split:nat.split)
done

theorem kernel_compile: includes Vars shows
 "pure t \<Longrightarrow> \<forall>i. \<sigma> i = V\<^isub>U i [] \<Longrightarrow> (compile t \<sigma>)! = t"
apply(induct arbitrary: \<sigma> pred:pure)
apply simp_all
apply(subst lift_compile) apply simp
apply(subst subst_ML_compile) apply simp
apply(subgoal_tac "(subst\<^bsub>ML\<^esub> (\<lambda>n. if n = 0 then V\<^isub>U 0 [] else V\<^bsub>ML\<^esub> (n - 1)) \<circ>
               (lift 0 \<circ> V\<^bsub>ML\<^esub> 0 ## \<sigma>)) = (\<lambda>a. V\<^isub>U a [])")
apply(simp)
apply(rule ext)
apply(simp add:cons_ML_def split:nat.split)
done

lemma kernel_subst_ML: includes Vars shows
  "pure t \<Longrightarrow> \<forall>i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i) \<Longrightarrow>
   (subst\<^bsub>ML\<^esub> \<sigma> (comp_open t))! = subst (kernel \<circ> \<sigma>) t"
proof(induct arbitrary: \<sigma> pred:pure)
  case (Lam t)
  have "lift 0 o V_ML = V_ML" by (simp add:expand_fun_eq)
  hence "(subst\<^bsub>ML\<^esub> \<sigma> (comp_open (\<Lambda> t)))! =
    \<Lambda> (subst\<^bsub>ML\<^esub> (lift 0 \<circ> V\<^bsub>ML\<^esub> 0 ## \<sigma>) (comp_open t)[V\<^isub>U 0 []/0]!)"
    using Lam by(simp add: lift_subst_ML comp_open_def lift_compile)
  also have "\<dots> = \<Lambda> (subst (V 0 ## (kernel \<circ> \<sigma>)) t)" using Lam
    by(simp add: subst_ML_comp subst_ext cons_ML_def cons_def kernel_lift_tm
      split:nat.split)
  also have "\<dots> = subst (kernel o \<sigma>) (\<Lambda> t)" by simp
  finally show ?case .
qed (simp_all add:comp_open_def)

lemma kernel_subst_ML_map: includes Vars shows
  "\<forall>t \<in> set ts. pure t \<Longrightarrow> \<forall>i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i) \<Longrightarrow>
   map kernel (map (subst\<^bsub>ML\<^esub> \<sigma>) (map comp_open ts)) =
   map (subst (kernel \<circ> \<sigma>)) ts"
by(simp add:list_eq_iff_nth_eq kernel_subst_ML)

lemma compR_tRed: "(nm, vs, v) : compR \<Longrightarrow> \<forall> i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i)
  \<Longrightarrow> C nm \<bullet>\<bullet> (map (subst\<^bsub>ML\<^esub> \<sigma>) (rev vs))! \<rightarrow>* (subst\<^bsub>ML\<^esub> \<sigma> v)!"
apply(auto simp add:compR_def rev_map)
apply(frule pure_R)
apply(subst kernel_subst_ML) apply fast+
apply(subst kernel_subst_ML_map) apply fast+
apply(rule r_into_rtrancl)
apply(erule tRed.intros)
done

section "Correctness"

(* Without this special rule one "also" in the next proof *diverges*,
   probably because of HOU. *)
lemma eq_tRed_trans: "s = t \<Longrightarrow> t \<rightarrow> t' \<Longrightarrow> s \<rightarrow> t'"
by simp

text{* Soundness of reduction: *}
theorem includes Vars shows Red_sound:
  "v \<Rightarrow> v' \<Longrightarrow> closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow> v! \<rightarrow>* v'! \<and> closed\<^bsub>ML\<^esub> 0 v'" and
  "vs \<Rightarrow> vs' \<Longrightarrow> \<forall>v\<in>set vs. closed\<^bsub>ML\<^esub> 0 v \<Longrightarrow>
   vs! \<rightarrow>* vs'! \<and> (\<forall>v'\<in>set vs'. closed\<^bsub>ML\<^esub> 0 v')"
proof(induct rule:Red_Redl.inducts)
  fix u v
  let ?v = "A_ML (Lam_ML u) [v]"
  assume cl: "closed\<^bsub>ML\<^esub> 0 (A_ML (Lam_ML u) [v])"
  let ?u' = "(lift_ml 0 u)[V\<^isub>U 0 []/0]"
  have "?v! = (\<Lambda>((?u')!)) \<bullet> (v !)" by simp
  also have "\<dots> \<rightarrow> (?u' !)[v!/0]" (is "_ \<rightarrow> ?R") by(rule tRed.intros)
  also(eq_tRed_trans) have "?R = u[v/0]!" using cl
    apply(cut_tac u = "u" and v = "v" in kernel_subst1)
    apply(simp_all)
    done
  finally have "kernel(A_ML (Lam_ML u) [v]) \<rightarrow>* kernel(u[v/0])" (is ?A)
    by(rule r_into_rtrancl)
  moreover have "closed\<^bsub>ML\<^esub> 0 (u[v/0])" (is "?C")
  proof -
    let ?\<sigma> = "\<lambda>n. if n = 0 then v else V_ML (n - 1)"
    let ?\<sigma>' = "\<lambda>n. v"
    have clu: "closed\<^bsub>ML\<^esub> (Suc 0) u" and clv: "closed\<^bsub>ML\<^esub> 0 v" using cl by simp+
    have "closed\<^bsub>ML\<^esub> 0 (subst\<^bsub>ML\<^esub> ?\<sigma>' u)"
      by (metis COMBK_def closed_ML_subst_ML clv)
    hence "closed\<^bsub>ML\<^esub> 0 (subst\<^bsub>ML\<^esub> ?\<sigma> u)"
      using subst_ML_coincidence[OF clu, of ?\<sigma> ?\<sigma>'] by auto
    thus ?thesis by simp
  qed
  ultimately show "?A \<and> ?C" ..
next
  fix \<sigma> :: "nat \<Rightarrow> ml" and nm vs v
  assume \<sigma>: "\<forall>i. closed\<^bsub>ML\<^esub> 0 (\<sigma> i)"  and compR: "(nm, vs, v) \<in> compR"
  have "map (subst V) (map (subst\<^bsub>ML\<^esub> \<sigma>) (rev vs)!) = map (subst\<^bsub>ML\<^esub> \<sigma>) (rev vs)!"
    by(simp add:list_eq_iff_nth_eq subst_V_kernel closed_ML_subst_ML[OF \<sigma>])
  with compR_tRed[OF compR \<sigma>]
  have "(C nm) \<bullet>\<bullet> ((map (subst\<^bsub>ML\<^esub> \<sigma>) (rev vs)) !) \<rightarrow>* (subst\<^bsub>ML\<^esub> \<sigma> v)!"
    by(simp add:subst_V_kernel closed_ML_subst_ML[OF \<sigma>])
  hence "A_ML (C_ML nm) (map (subst\<^bsub>ML\<^esub> \<sigma>) vs)! \<rightarrow>* subst\<^bsub>ML\<^esub> \<sigma> v!" (is ?A)
    by(simp add:rev_map)
  moreover
  have "closed\<^bsub>ML\<^esub> 0 (subst\<^bsub>ML\<^esub> \<sigma> v)" (is ?C) by(metis closed_ML_subst_ML \<sigma>)
  ultimately show "?A \<and> ?C" ..
qed (auto simp:tRed_list_foldl_At tRed_rev rev_map[symmetric])

theorem Redt_sound: includes Vars
 shows "t \<Rightarrow> t' \<Longrightarrow> closed\<^bsub>ML\<^esub> 0 t \<Longrightarrow> kernelt t \<rightarrow>* kernelt t'  \<and> closed\<^bsub>ML\<^esub> 0 t'"
proof(induct rule:Redt.inducts)
  case term_C thus ?case
    by (auto simp:closed_tm_ML_foldl_At map_compose[symmetric])
next
  case term_V thus ?case
    by (auto simp:map_compose[symmetric]closed_tm_ML_foldl_At)
next
  case (term_Clo vf vs n)
  hence "(lift 0 vf!) \<bullet>\<bullet> map kernel (rev (map (lift 0) vs))
         = lift 0 (vf! \<bullet>\<bullet> (rev vs)!)"
    apply (simp add:kernel_lift_tm list_eq_iff_nth_eq)
    apply(simp add:rev_nth rev_map kernel_lift_tm)
    done
  hence "term (Clo vf vs n)! \<rightarrow>*
       \<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^isub>U 0 [])))!"
    using term_Clo
    by(simp del:lift_foldl_At add: r_into_rtrancl tRed.intros(2))
  moreover
  have "closed\<^bsub>ML\<^esub> 0 (\<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^isub>U 0 []))))"
    using term_Clo by simp
  ultimately show ?case ..
next
  case ctxt_term thus ?case by simp (metis Red_sound)
qed auto

corollary kernel_inv: includes Vars shows
 "(t :: tm) \<Rightarrow>* t' \<Longrightarrow> closed\<^bsub>ML\<^esub> 0 t \<Longrightarrow> t! \<rightarrow>* t'! \<and> closed\<^bsub>ML\<^esub> 0 t' "
apply(induct rule: rtrancl.induct)
apply (metis rtrancl_eq_or_trancl)
apply (metis Redt_sound rtrancl_trans)
done

lemma  closed_ML_compile:
  "pure t \<Longrightarrow> \<forall>i. closed\<^bsub>ML\<^esub> n (\<sigma> i) \<Longrightarrow> closed\<^bsub>ML\<^esub> n (compile t \<sigma>)"
proof(induct arbitrary:n \<sigma> pred:pure)
  case (Lam t)
  have 1: "\<forall>i. closed\<^bsub>ML\<^esub> (Suc n) ((V_ML 0 ## \<sigma>) i)" using Lam(3-)
    by (auto simp: closed_ML_Suc cons_ML_def split:nat.split)
    show ?case using Lam(2)[OF 1] by simp
qed simp_all

theorem nbe_correct: includes Vars
assumes "pure t" and "pure t'"
and "term (comp_fixed t) \<Rightarrow>* t'" shows "t \<rightarrow>* t'"
proof -
  have ML_cl: "closed\<^bsub>ML\<^esub> 0 (term (comp_fixed t))"
    by (simp add: closed_ML_compile[OF `pure t`])
  have "(term (comp_fixed t))! = t"
    using kernel_compile[OF `pure t`] by simp
  moreover have "term (comp_fixed t)! \<rightarrow>* t'!"
    using kernel_inv[OF assms(3) ML_cl] by auto
  ultimately have "t \<rightarrow>* t'!" by simp
  thus ?thesis using kernel_pure[OF `pure t'`] by simp
qed

inductive normal :: "tm \<Rightarrow> bool" where
"ALL t:set ts. normal t \<Longrightarrow> normal(V x \<bullet>\<bullet> ts)" |
"normal t \<Longrightarrow> normal(\<Lambda> t)" |
"ALL t:set ts. normal t \<Longrightarrow>
 ALL \<sigma>. ALL (nm',ls,r):R. \<not>(nm = nm' \<and> take (size ls) ts = map (subst \<sigma>) ls)
 \<Longrightarrow> normal(C nm \<bullet>\<bullet> ts)"

fun C_normal where
"C_normal(C\<^isub>U nm vs) = ((\<forall>v \<in> set vs. C_normal v) \<and> no_match_compR nm vs)" |
"C_normal (C\<^bsub>ML\<^esub> _) = True" |
"C_normal (V\<^bsub>ML\<^esub> _) = True" |
"C_normal (A\<^bsub>ML\<^esub> v vs) = (C_normal v \<and> (\<forall>v \<in> set vs. C_normal v))" |
"C_normal (Lam\<^bsub>ML\<^esub> v) = C_normal v" |
"C_normal (V\<^isub>U x vs) = (\<forall>v \<in> set vs. C_normal v)" |
"C_normal (Clo v vs _) = (C_normal v \<and> (\<forall>v \<in> set vs. C_normal v))" |
"C_normal (apply u v) = (C_normal u \<and> C_normal v)"

lemma C_normal_inv: "v \<Rightarrow> v' \<Longrightarrow> C_normal v \<Longrightarrow> C_normal v'" and
      "vs \<Rightarrow> vs' \<Longrightarrow> \<forall>v\<in>set vs. C_normal v \<Longrightarrow> \<forall>v'\<in>set vs. C_normal v'"
apply(induct rule:Red_Redl.inducts)
apply(simp_all)
sorry

lemma not_pure_term[simp]: "~ pure(term v)"
proof
  assume "pure(term v)" thus False
  proof cases qed auto
qed

abbreviation RedMLs :: "tm list \<Rightarrow> tm list \<Rightarrow> bool" (infix "[\<Rightarrow>*]" 50) where
"ss [\<Rightarrow>*] ts == size ss = size ts \<and> (\<forall>i<size ss. ss!i \<Rightarrow>* ts!i)"

lemma includes Vars
assumes "no_match_compR nm vs" "map term (rev vs) [\<Rightarrow>*] ts" "C nm \<bullet>\<bullet> ts \<Rightarrow>* s"
shows "EX ss. s = C nm \<bullet>\<bullet> ss \<and> ts [\<Rightarrow>*] ss"
sorry

lemma nbe_C_normal: includes Vars
assumes "term v \<Rightarrow>* t'" "C_normal v" "pure t'" shows "normal t'"
proof -
  { fix t t' i v
    assume "(t,t') : Redt^i"
    hence "t = term v \<Longrightarrow> C_normal v \<Longrightarrow> pure t' \<Longrightarrow> normal t'"
    proof(induct i arbitrary: t t' v)
      case 0 thus ?case by auto
    next
      case (Suc i)
      then obtain s where "t \<Rightarrow> s" "(s,t') : Redt^i"
	by(blast dest:rel_pow_Suc_D2)
      hence "term v \<Rightarrow> s" using Suc by simp
      thus ?case
      proof cases
	case (term_C nm vs)
	have "\<forall>(nm',vs',v') \<in> compR. nm=nm' \<longrightarrow> no_match\<^bsub>ML\<^esub> vs' vs" sorry
	show ?thesis using Suc term_C

  next
    case term_V show ?thesis sorry
  next
    case term_Clo show ?thesis sorry
  next
    case ctxt_term
    thus ?thesis using 2 C_normal_inv by auto
  qed auto
qed

    }
    thus ?thesis using assms unfolding rtrancl_is_UN_rel_pow by blast
qed

  case (2 t s v)
  hence "term v \<Rightarrow> s" by simp
  thus ?case
  proof cases
    case (term_C nm vs)
    have "\<forall>(nm',vs',v') \<in> compR. nm=nm' \<longrightarrow> no_match\<^bsub>ML\<^esub> vs' vs" sorry
    show ?thesis using 2 term_C
"

  next
    case term_V show ?thesis sorry
  next
    case term_Clo show ?thesis sorry
  next
    case ctxt_term
    thus ?thesis using 2 C_normal_inv by auto
  qed auto
qed

using `t \<Rightarrow>* t'`
proof(induct arbitrary: v rule:converse_rtrancl_induct)
  case 1 thus ?case by simp
next
  case (2 t s v)
  hence "term v \<Rightarrow> s" by simp
  thus ?case
  proof cases
    case (term_C nm vs)
    have "\<forall>(nm',vs',v') \<in> compR. nm=nm' \<longrightarrow> no_match\<^bsub>ML\<^esub> vs' vs" sorry
    show ?thesis using 2 term_C
"

  next
    case term_V show ?thesis sorry
  next
    case term_Clo show ?thesis sorry
  next
    case ctxt_term
    thus ?thesis using 2 C_normal_inv by auto
  qed auto
qed

theorem nbe_normal: includes Vars
assumes "pure t" and "pure t'"
and "term (comp_fixed t) \<Rightarrow>* t'" shows "normal t'"



(*<*)
end
(*>*)