theory Prover
imports Main
begin

subsection "Formulas"

type_synonym pred = nat

type_synonym var = nat

datatype form = 
    PAtom pred "var list"
  | NAtom pred "var list"
  | FConj form form
  | FDisj form form
  | FAll form
  | FEx form

primrec preSuc :: "nat list \<Rightarrow> nat list"
where
  "preSuc [] = []"
| "preSuc (a#list) = (case a of 0 \<Rightarrow> preSuc list | Suc n \<Rightarrow> n#(preSuc list))"

primrec fv :: "form \<Rightarrow> var list" \<comment> \<open>shouldn't need to be more constructive than this\<close>
where
  "fv (PAtom p vs) = vs"
| "fv (NAtom p vs) = vs"
| "fv (FConj f g) = (fv f) @ (fv g)"
| "fv (FDisj f g) = (fv f) @ (fv g)"
| "fv (FAll f) = preSuc (fv f)"
| "fv (FEx f) = preSuc (fv f)"

definition
  bump :: "(var \<Rightarrow> var) \<Rightarrow> (var \<Rightarrow> var)" \<comment> \<open>substitute a different var for 0\<close> where
  "bump \<phi> y = (case y of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (\<phi> n))"

primrec subst :: "(nat \<Rightarrow> nat) \<Rightarrow> form \<Rightarrow> form"
where
  "subst r (PAtom p vs) = (PAtom p (map r vs))"
| "subst r (NAtom p vs) = (NAtom p (map r vs))"
| "subst r (FConj f g) = FConj (subst r f) (subst r g)"
| "subst r (FDisj f g) = FDisj (subst r f) (subst r g)"
| "subst r (FAll f) = FAll (subst (bump r) f)"
| "subst r (FEx f) = FEx (subst (bump r) f)"

lemma size_subst[simp]: "\<forall>m. size (subst m f) = size f"
  by (induct f) (force+)

definition
  finst :: "form \<Rightarrow> var \<Rightarrow> form" where
  "finst body w = (subst (\<lambda> v. case v of 0 \<Rightarrow> w | Suc n \<Rightarrow> n) body)"

lemma size_finst[simp]: "size (finst f m) = size f"
  by (simp add: finst_def)

type_synonym seq = "form list"

type_synonym nform = "nat * form"

type_synonym nseq = "nform list"

definition
  s_of_ns :: "nseq \<Rightarrow> seq" where
  "s_of_ns ns = map snd ns"

definition
  ns_of_s :: "seq \<Rightarrow> nseq" where
  "ns_of_s s = map (\<lambda> x. (0,x)) s"

definition
  sfv :: "seq \<Rightarrow> var list" where
  "sfv s = concat (map fv s)"

lemma sfv_nil: "sfv [] = []"
  by(force simp: sfv_def)

lemma sfv_cons: "sfv (a#list) = (fv a) @ (sfv list)" 
  by(force simp: sfv_def)

primrec maxvar :: "var list \<Rightarrow> var"
where
  "maxvar [] = 0"
| "maxvar (a#list) = max a (maxvar list)"

lemma maxvar: "\<forall>v \<in> set vs. v \<le> maxvar vs"
  by (induct vs) (auto simp: max_def)

definition
  newvar :: "var list \<Rightarrow> var" where
  "newvar vs = (if vs = [] then 0 else Suc (maxvar vs))"
  \<comment> \<open>note that for newvar to be constructive, need an operation to get a different var from a given set\<close>

lemma newvar: "newvar vs \<notin> (set vs)"
  using length_pos_if_in_set maxvar newvar_def by force

primrec subs :: "nseq \<Rightarrow> nseq list"
  where
    "subs [] = [[]]"
  | "subs (x#xs) =
  (let (m,f) = x in
                case f of
                  PAtom p vs \<Rightarrow> if NAtom p vs \<in> set (map snd xs) then [] else [xs@[(0,PAtom p vs)]]
                  | NAtom p vs \<Rightarrow> if PAtom p vs \<in> set (map snd xs) then [] else [xs@[(0,NAtom p vs)]] 
                  | FConj f g \<Rightarrow> [xs@[(0,f)],xs@[(0,g)]]
                  | FDisj f g \<Rightarrow> [xs@[(0,f),(0,g)]]
                  | FAll f \<Rightarrow> [xs@[(0,finst f (newvar (sfv (s_of_ns (x#xs)))))]]
                  | FEx f \<Rightarrow> [xs@[(0,finst f m),(Suc m,FEx f)]]
              )"


subsection "Derivations"

primrec is_axiom :: "seq \<Rightarrow> bool"
where
  "is_axiom [] = False"
| "is_axiom (a#list) = ((\<exists>p vs. a = PAtom p vs \<and> NAtom p vs \<in> set list) \<or> (\<exists>p vs. a = NAtom p vs \<and> PAtom p vs \<in> set list))"

inductive_set
  deriv :: "nseq \<Rightarrow> (nat * nseq) set"
  for s :: nseq
where
  init: "(0,s) \<in> deriv s"
| step: "(n,x) \<in> deriv s \<Longrightarrow> y \<in> set (subs x) \<Longrightarrow> (Suc n,y) \<in> deriv s"
  \<comment> \<open>the closure of the branch at isaxiom\<close>

inductive_cases Suc_derivE: "(Suc n, x) \<in> deriv s"

declare init [simp,intro]
declare step [intro]

lemma patom:  "(n,(m,PAtom p vs)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,PAtom p vs)#xs)) \<Longrightarrow> (Suc n,xs@[(0,PAtom p vs)]) \<in> deriv(nfs)"
  and natom:  "(n,(m,NAtom p vs)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,NAtom p vs)#xs)) \<Longrightarrow> (Suc n,xs@[(0,NAtom p vs)]) \<in> deriv(nfs)"
  and fconj1: "(n,(m,FConj f g)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,FConj f g)#xs)) \<Longrightarrow> (Suc n,xs@[(0,f)]) \<in> deriv(nfs)"
  and fconj2: "(n,(m,FConj f g)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,FConj f g)#xs)) \<Longrightarrow> (Suc n,xs@[(0,g)]) \<in> deriv(nfs)"
  and fdisj:  "(n,(m,FDisj f g)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,FDisj f g)#xs)) \<Longrightarrow> (Suc n,xs@[(0,f),(0,g)]) \<in> deriv(nfs)"
  and fall:   "(n,(m,FAll f)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,FAll f)#xs)) \<Longrightarrow> (Suc n,xs@[(0,finst f (newvar (sfv (s_of_ns ((m,FAll f)#xs)))))]) \<in> deriv(nfs)" 
  and fex:    "(n,(m,FEx f)#xs) \<in> deriv(nfs) \<Longrightarrow> \<not> is_axiom (s_of_ns ((m,FEx f)#xs)) \<Longrightarrow> (Suc n,xs@[(0,finst f m),(Suc m,FEx f)]) \<in> deriv(nfs)"
  by (auto simp: s_of_ns_def)
  
lemma deriv0[simp]: "(0,x) \<in> deriv y \<longleftrightarrow> (x = y)"
  using deriv.cases by blast

lemma deriv_exists: 
  assumes "(n, x) \<in> deriv s" "x \<noteq> []" "\<not> is_axiom (s_of_ns x)"
  shows "\<exists>y. (Suc n, y) \<in> deriv s \<and> y \<in> set (subs x)"
proof (cases x)
  case (Cons ab list)
  show ?thesis 
  proof (cases ab)
    case (Pair a b)
    with Cons assms show ?thesis 
      by(cases b; fastforce simp: s_of_ns_def)
  qed
qed (use assms in auto)

lemma deriv_upwards: "(n,list) \<in> deriv s \<Longrightarrow> \<not> is_axiom (s_of_ns (list)) \<Longrightarrow> (\<exists>zs. (Suc n, zs) \<in> deriv s \<and> zs \<in> set (subs list))"
  by (metis deriv.step deriv_exists list.set_intros(1) subs.simps(1))

lemma deriv_downwards:
  assumes "(Suc n, x) \<in> deriv s"
  shows "\<exists>y. (n, y) \<in> deriv s \<and> x \<in> set (subs y) \<and> \<not> is_axiom (s_of_ns y)"
proof -
  obtain x' where x': "(n, x') \<in> deriv s" "x \<in> set (subs x')"
    using Suc_derivE assms by blast
  have False if "is_axiom (s_of_ns x')"
  proof (cases x')
    case (Cons ab list)
    show ?thesis 
    proof (cases ab)
      case (Pair a b)
      with Cons x' that assms show ?thesis 
        by (cases b) (auto simp: s_of_ns_def)
    qed
  next
    case Nil
    then show ?thesis
      using s_of_ns_def that by auto
  qed 
  then show ?thesis
    using x' by blast
qed

lemma deriv_deriv_child: "(Suc n,x) \<in> deriv y = (\<exists>z. z \<in> set (subs y) \<and> \<not> is_axiom (s_of_ns y) \<and> (n,x) \<in> deriv z)"
proof (induction n arbitrary: x y)
  case 0
  then show ?case
    using deriv_downwards by (force elim: Suc_derivE)
next
  case (Suc n)
  then show ?case
    by (meson deriv_downwards deriv.step) 
qed

lemmas not_is_axiom_subs = patom natom fconj1 fconj2 fdisj fall fex

lemma deriv_progress:
  assumes "(n, a # list) \<in> deriv s"
    and "\<not> is_axiom (s_of_ns (a # list))"
  shows "\<exists>zs. (Suc n, list @ zs) \<in> deriv s"
  by (metis assms form.exhaust surj_pair not_is_axiom_subs)

definition
  inc :: "nat * nseq \<Rightarrow> nat * nseq" where
  "inc = (\<lambda>(n,fs). (Suc n, fs))"

lemma deriv: "deriv y = insert (0,y) (inc ` (Union (deriv ` {w. \<not> is_axiom (s_of_ns y) \<and> w \<in> set (subs y)})))"
    by (auto simp: inc_def deriv_deriv_child image_iff; metis case_prod_conv deriv.cases deriv_deriv_child)

lemma deriv_is_axiom: "is_axiom (s_of_ns s) \<Longrightarrow> deriv s = {(0,s)}"
  using deriv by blast
   
lemma is_axiom_finite_deriv: "is_axiom (s_of_ns s) \<Longrightarrow> finite (deriv s)"
  by (simp add: deriv_is_axiom) 


subsection "Failing path"

primrec failing_path :: "(nat * nseq) set \<Rightarrow> nat \<Rightarrow> (nat * nseq)"
where
  "failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (deriv (snd x)) \<and> \<not> is_axiom (s_of_ns (snd x)))"
| "failing_path ns (Suc n) = (let fn = failing_path ns n in 
  (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (subs (snd fn)) \<and> infinite (deriv (snd fsucn)) \<and> \<not> is_axiom (s_of_ns (snd fsucn))))"

locale FailingPath = 
  fixes s and f 
  assumes inf: "infinite (deriv s)"
  assumes f: "f = failing_path (deriv s)"

begin

lemma f0: "f 0 \<in> (deriv s) \<and> fst (f 0) = 0 \<and> 
           infinite (deriv (snd (f 0))) \<and> \<not> is_axiom (s_of_ns (snd (f 0)))"
  by (metis (mono_tags, lifting) inf deriv0 f failing_path.simps(1) fst_conv
      is_axiom_finite_deriv snd_conv someI_ex)

lemma fSuc:
  assumes fn: "f n \<in> deriv s" "fst (f n) = n"
    and inf: "infinite (deriv (snd (f n)))"
    and "\<not> is_axiom (s_of_ns (snd (f n)))"
  shows "f (Suc n) \<in> deriv s \<and> fst (f (Suc n)) = Suc n \<and> snd (f (Suc n)) \<in> set (subs (snd (f n))) \<and> infinite (deriv (snd (f (Suc n)))) \<and> \<not> is_axiom (s_of_ns (snd (f (Suc n))))"
proof -
  have  "infinite (\<Union>(deriv ` {w. \<not> is_axiom (s_of_ns (snd (f n))) \<and> w \<in> set (subs (snd (f n)))}))"
    by (metis inf deriv finite_imageI finite_insert)
  then obtain y where "y \<in> set (subs (snd (f n)))" "infinite (deriv y)"
    by fastforce
  then have "\<exists>x. x \<in> deriv s \<and> fst x = Suc n \<and>
        snd x \<in> set (subs (snd (failing_path (deriv s) n))) \<and>
        infinite (deriv (snd x)) \<and> \<not> is_axiom (s_of_ns (snd x))"
    by (metis deriv.step f fn fst_conv is_axiom_finite_deriv prod.exhaust_sel snd_conv)
  then show ?thesis
    by (metis (mono_tags, lifting) f failing_path.simps(2) someI_ex)
qed

lemma is_path_f_0: "f 0 = (0,s)"
  by (metis deriv0 f0 split_pairs)

lemma is_path_f': "f n \<in> deriv s \<and> fst (f n) = n \<and> infinite (deriv (snd (f n))) \<and> \<not> is_axiom (s_of_ns (snd (f n)))"
  by (induction n) (auto simp: f0 fSuc)

lemma is_path_f: "f n \<in> deriv s \<and> fst (f n) = n \<and> (snd (f (Suc n))) \<in> set (subs (snd (f n))) \<and> infinite (deriv (snd (f n)))"
  using fSuc is_path_f' by blast

end

subsection "Models"

typedecl U

type_synonym model = "U set * (pred \<Rightarrow> U list \<Rightarrow> bool)"

type_synonym env = "var \<Rightarrow> U" 

primrec FEval :: "model \<Rightarrow> env \<Rightarrow> form \<Rightarrow> bool"
where
  "FEval MI e (PAtom P vs) = (let IP = (snd MI) P in IP (map e vs))"
| "FEval MI e (NAtom P vs) = (let IP = (snd MI) P in \<not> (IP (map e vs)))"
| "FEval MI e (FConj f g) = ((FEval MI e f) \<and> (FEval MI e g))"
| "FEval MI e (FDisj f g) = ((FEval MI e f) \<or> (FEval MI e g))"
| "FEval MI e (FAll f) = (\<forall>m \<in> (fst MI). FEval MI (\<lambda> y. case y of 0 \<Rightarrow> m | Suc n \<Rightarrow> e n) f)" 
| "FEval MI e (FEx f) = (\<exists>m \<in> (fst MI). FEval MI (\<lambda> y. case y of 0 \<Rightarrow> m | Suc n \<Rightarrow> e n) f)"

lemma preSuc[simp]: "Suc n \<in> set A = (n \<in> set (preSuc A))"
  by (induction A) (auto simp: split: nat.splits)

lemma FEval_cong: "(\<forall>x \<in> set (fv A). e1 x = e2 x) \<Longrightarrow> FEval MI e1 A = FEval MI e2 A"
proof (induction A arbitrary: e1 e2)
  case (PAtom x1 x2)
  then show ?case
    by (metis FEval.simps(1) fv.simps(1) map_cong)
next
  case (NAtom x1 x2)
  then show ?case
    by simp (metis list.map_cong0)
next
  case (FConj A1 A2)
  then show ?case 
    by simp blast
next
  case (FDisj A1 A2)
  then show ?case
    by simp blast
next
  case (FAll A)
  then show ?case
    by (metis (no_types, lifting) FEval.simps(5) Nitpick.case_nat_unfold One_nat_def Suc_pred fv.simps(5) gr0I preSuc)
next
  case (FEx A)
  then show ?case
    by (metis (no_types, lifting) FEval.simps(6) Nitpick.case_nat_unfold One_nat_def Suc_pred fv.simps(6) gr0I preSuc)
qed


primrec SEval :: "model \<Rightarrow> env \<Rightarrow> form list \<Rightarrow> bool"
where
  "SEval m e [] = False"
| "SEval m e (x#xs) = (FEval m e x \<or> SEval m e xs)"

lemma SEval_def2: "SEval m e s = (\<exists>f. f \<in> set s \<and> FEval m e f)"
  by (induct s) auto

lemma SEval_append: "SEval m e (xs@ys) \<longleftrightarrow> SEval m e xs \<or> SEval m e ys"
  by (induct xs) auto

lemma SEval_cong: "(\<forall>x \<in> set (sfv s). e1 x = e2 x) \<Longrightarrow> SEval m e1 s = SEval m e2 s"
proof (induction s)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  then show ?case
    by (metis SEval.simps(2) FEval_cong Un_iff sfv_cons set_append)
qed

definition
  is_env :: "model \<Rightarrow> env \<Rightarrow> bool"
    where "is_env MI e \<equiv> (\<forall>x. e x \<in> (fst MI))"

definition
  Svalid :: "form list \<Rightarrow> bool" 
    where "Svalid s \<equiv> (\<forall>MI e. is_env MI e \<longrightarrow> SEval MI e s)"


subsection "Soundness"

lemma FEval_subst: "(FEval MI e (subst f A)) = (FEval MI (e \<circ> f) A)"
proof -
  have \<section>: "(case bump f k of 0 \<Rightarrow> m | Suc x \<Rightarrow> e x) = 
           (case k of 0 \<Rightarrow> m | Suc n \<Rightarrow> e (f n))" 
    if "m \<in> fst MI" for m k e f
    using that by (simp add: bump_def split: nat.splits)
  show ?thesis
  proof (induction A arbitrary: e f)
    case (FAll A)
    with \<section> show ?case by simp
  next
    case (FEx A)
    with \<section> show ?case by simp
  qed (use FEval.simps in auto)
qed


lemma FEval_finst: "FEval mo e (finst A u) = FEval mo (case_nat (e u) e) A"
proof -
  have "(e \<circ> case_nat u (\<lambda>n. n)) = (case_nat (e u) e)"
    by (simp add: fun_eq_iff split: nat.splits)
  then show ?thesis
    by (simp add: FEval_subst finst_def)
qed

lemma sound_FAll:
  assumes "u \<notin> set (sfv (FAll f # s))"
    and "Svalid (s @ [finst f u])"
  shows "Svalid (FAll f # s)"
proof -
  have "SEval (M,I) e (FAll f # s)"
    if e: "is_env (M,I) e" for M I e
  proof -
    consider "SEval (M, I) e s" | "FEval (M, I) e (finst f u)" "\<not> SEval (M, I) e s"
      using SEval_append Svalid_def assms e by fastforce
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        by auto
    next
      case 2
      have "FEval (M, I) (case_nat m e) f"
        if "m \<in> M" for m
      proof -
        have "FEval (M, I) (case_nat ((e(u := m)) u) (e(u := m))) f" (is ?P)
          using assms e \<open>m \<in> M\<close> 2
          apply (simp add: Svalid_def SEval_append is_env_def FEval_finst sfv_cons)
          by (smt (verit, best) SEval_cong fun_upd_apply)
        moreover have "?P = FEval (M, I) (case_nat m e) f"
          using assms
          by (intro FEval_cong strip) (auto simp: sfv_cons split: nat.splits)
        ultimately show ?thesis
          by auto
      qed
      then show ?thesis
        by (auto simp: SEval_append 2)
    qed
  qed
  then show ?thesis 
    by (simp add: Svalid_def)
qed


lemma sound_FEx: "Svalid (s@[finst f u,FEx f]) \<Longrightarrow> Svalid (FEx f#s)"
  unfolding Svalid_def
  by (metis FEval.simps(6) FEval_finst SEval.simps SEval_append is_env_def)

lemma inj_inc: "inj inc"
  by (simp add: Prover.inc_def inj_def)

lemma finite_inc: "finite (inc ` X) = finite X"
  by (metis finite_imageD finite_imageI inj_def inj_inc inj_on_def)

lemma finite_deriv_deriv: "finite (deriv s) \<Longrightarrow> finite  (deriv ` {w. \<not> is_axiom (s_of_ns s) \<and> w \<in> set (subs s)})"
  by simp

definition
  init :: "nseq \<Rightarrow> bool" where
  "init s = (\<forall>x \<in> (set s). fst x = 0)"

definition
  is_FEx :: "form \<Rightarrow> bool" where
  "is_FEx f = (case f of
      PAtom p vs \<Rightarrow> False
    | NAtom p vs \<Rightarrow> False
    | FConj f g \<Rightarrow> False
    | FDisj f g \<Rightarrow> False
    | FAll f \<Rightarrow> False
    | FEx f \<Rightarrow> True)"

lemma is_FEx[simp]: "\<not> is_FEx (PAtom p vs)
  \<and> \<not> is_FEx (NAtom p vs)
  \<and> \<not> is_FEx (FConj f g)
  \<and> \<not> is_FEx (FDisj f g)
  \<and> \<not> is_FEx (FAll f)"
  by(force simp: is_FEx_def)

lemma index0: "\<lbrakk>init s; (n, u) \<in> deriv s; (m, A) \<in> set u; \<not> is_FEx A\<rbrakk> \<Longrightarrow> m = 0"
proof(induction n arbitrary: u)
  case 0
  then show ?case
    using init_def by auto
next
  case (Suc n)
  then obtain y where y: "(n, y) \<in> deriv s" "u \<in> set (subs y)" "\<not> is_axiom (s_of_ns y)"
    using deriv_downwards by blast
  have ?case if "y = Cons (a,b) list" for a b list
    using that y Cons Suc 
    by (fastforce simp: is_FEx_def split: form.splits if_splits)
  then show ?case
    using Suc y
    by (metis empty_iff list.set(1) neq_Nil_conv set_ConsD subs.simps(1)
        surjective_pairing) 
qed

lemma soundness':
  assumes "init s" "\<And>y u. (y, u) \<in> deriv s \<Longrightarrow> y \<le> m"
  shows "\<lbrakk>h = m-n; (n, t) \<in> deriv s\<rbrakk> \<Longrightarrow> Svalid (s_of_ns t)"
proof (induction h arbitrary: n t)
  case 0
  show ?case
  proof (cases "m=n")
    case True
    show ?thesis
    proof (cases "is_axiom (s_of_ns t)")
      case True
      then have *: "is_axiom (map snd t)"
        using s_of_ns_def by force
      have ?thesis if "t = Cons u v" for u v
        using * that 0
        by (simp add: Svalid_def SEval_def2 s_of_ns_def) (metis FEval.simps(1,2))
      then show ?thesis
        by (metis True is_axiom.simps(1) list.exhaust list.simps(8) s_of_ns_def)
    next
      case False
      with "0.prems" True assms show ?thesis
        by (metis deriv_upwards not_less_eq_eq)
    qed
  next
    case False
    with "0.prems" assms show ?thesis by force
  qed
next
  case (Suc h)
  show ?case
  proof (cases "is_axiom (s_of_ns t)")
    case True
    have "SEval (M, I) e (map snd ((u, v) # list))"
      if "t = (u, v) # list" "is_env (M, I) e" for u v list M I e
      using that SEval_def2 True s_of_ns_def by fastforce
    with True show ?thesis
      unfolding Svalid_def s_of_ns_def
      by (metis Nil_is_map_conv is_axiom.simps(1) list.exhaust surjective_pairing)
  next
    case False
    show ?thesis
    proof (cases t)
      case Nil
      with Suc assms show ?thesis
        apply simp
        by (metis Suc_leD deriv.step diff_Suc_Suc diff_diff_cancel diff_le_self
            list.set_intros(1) subs.simps(1))
    next
      case (Cons u v)
      have ?thesis if "u = (M,fm)" for M fm 
        using that
      proof (induction fm)
        case (PAtom p vs)
        then have "(Suc n, v @ [(0, PAtom p vs)]) \<in> deriv s"
          using False Suc.prems local.Cons patom by blast
        with PAtom show ?case
          using Suc.IH [of "Suc n" "v @ [(0, PAtom p vs)]"] Suc.prems
          by (fastforce simp: Svalid_def SEval_append Cons s_of_ns_def)
      next
        case (NAtom p vs)
        then have "(Suc n, v @ [(0, NAtom p vs)]) \<in> deriv s"
          using False Suc.prems local.Cons natom by blast
        with NAtom show ?case
          using Suc.IH [of "Suc n" "v @ [(0, NAtom p vs)]"] Suc.prems
          by (fastforce simp: Svalid_def SEval_append Cons s_of_ns_def)
      next
        case (FConj fm1 fm2)
        then obtain "(Suc n, v @ [(0, fm1)]) \<in> deriv s" "(Suc n, v @ [(0, fm2)]) \<in> deriv s"
          using Suc.prems local.Cons by force
        with FConj show ?case
          using Suc.IH [of "Suc n" "v @ [(0, fm1)]"] Suc.prems
          using Suc.IH [of "Suc n" "v @ [(0, fm2)]"] assms
          apply (simp add: Cons s_of_ns_def Svalid_def SEval_append)
          by (metis Suc_diff_le diff_Suc_1' diff_Suc_Suc)
      next
        case (FDisj fm1 fm2)
        then have "(Suc n, v @ [(0, fm1),(0, fm2)]) \<in> deriv s"
          using Suc.prems local.Cons by force
        with FDisj show ?case
          using Suc.IH [of "Suc n" "v @ [(0, fm1),(0, fm2)]"] Suc.prems assms
          apply (simp add: Cons s_of_ns_def Svalid_def SEval_append)
          by (metis Suc_diff_le diff_Suc_1' diff_Suc_Suc)
      next
        case (FAll fm)
        then have "M=0"
          using Suc.prems index0 Cons assms by force
        have "newvar (sfv (s_of_ns t)) \<notin> set (sfv (s_of_ns t))"
          by (simp add: newvar)
        with FAll \<open>M=0\<close> show ?case
          using Suc.IH [of "Suc n" "v @ [(0, finst fm (newvar (sfv (s_of_ns t))))]"] Suc.prems
          by (force simp: Cons s_of_ns_def fall sound_FAll)
      next
        case (FEx fm)
        then have "(Suc n, v @ [(0, finst fm M), (Suc M, FEx fm)]) \<in> deriv s"
          using Suc.prems local.Cons by auto
        with FEx Suc have "Svalid (s_of_ns (v@[(0,finst fm M), (Suc M, FEx fm)]))"
          by (metis diff_Suc nat.case(2))
        with FEx show ?case
          by (simp add: local.Cons s_of_ns_def sound_FEx)
      qed
      then show ?thesis
        using surjective_pairing by blast
    qed
  qed
qed

lemma s_of_ns_inverse[simp]: "s_of_ns (ns_of_s s) = s"
  by (induct s) (simp_all add: s_of_ns_def ns_of_s_def)

lemma soundness: 
  assumes "finite (deriv (ns_of_s s))" shows "Svalid s"
proof -
  obtain x where x: "x \<in> fst ` deriv (ns_of_s s)" 
    "\<And>y. y \<in> fst ` deriv (ns_of_s s) \<Longrightarrow> y \<le> x"
    by (metis assms deriv.init empty_iff finite_imageI image_eqI eq_Max_iff)
  have "Svalid (s_of_ns (ns_of_s s))"
  proof (intro soundness')
    show "init (ns_of_s s)"
    by (simp add: init_def ns_of_s_def)
  next
    fix y u
    assume "(y, u) \<in> deriv (ns_of_s s)"
    with x show "y \<le> x"
      by fastforce
  qed (use assms x in force)+
  then show ?thesis
    by auto
qed

subsection "Contains, Considers"

definition
  "contains" :: "(nat \<Rightarrow> (nat*nseq)) \<Rightarrow> nat \<Rightarrow> nform \<Rightarrow> bool" where
  "contains f n nf \<equiv> (nf \<in> set (snd (f n)))"

definition
  considers :: "(nat \<Rightarrow> (nat*nseq)) \<Rightarrow> nat \<Rightarrow> nform \<Rightarrow> bool" where
  "considers f n nf \<equiv> (case snd (f n) of [] \<Rightarrow> False | (x#xs) \<Rightarrow> x = nf)"

context FailingPath
begin

lemma progress:
  assumes "snd (f n) = a # list"
    shows "\<exists>zs'. snd (f (Suc n)) = list @ zs'"
proof -
  have "(snd (f (Suc n))) \<in> set (subs (snd (f n)))"
    using is_path_f by blast
  then have ?thesis if "a = (M,I)" for M I
    using assms that
    by (cases I) (auto simp: split: if_splits)
  then show ?thesis
    by fastforce
qed

lemma contains_considers': 
  shows "snd (f n) = xs@y#ys \<Longrightarrow> \<exists>m zs'. snd (f (n+m)) = y#zs'"
proof (induction xs arbitrary: n ys)
  case Nil
  then show ?case
    by (metis add.right_neutral append_Nil)
next
  case (Cons MI v)
  then obtain zs' where "snd (f (Suc n)) = (v @ y # ys) @ zs'"
    using progress Cons.prems
    by (metis append_Cons)
  then show ?case
    by (metis Cons.IH add_Suc_shift append_Cons append_assoc)
qed

lemma contains_considers:
  "contains f n y \<Longrightarrow> (\<exists>m. considers f (n+m) y)"
  unfolding contains_def considers_def
  by (smt (verit, ccfv_threshold) list.simps(5) FailingPath.contains_considers' FailingPath_axioms
      split_list_first)


lemma contains_propagates_patoms:
 "contains f n (0, PAtom p vs) \<Longrightarrow> contains f (n+q) (0, PAtom p vs)"
proof(induction q)
  case 0
  then show ?case
    by auto
next
  case (Suc q)
  then have \<section>: "\<not> is_axiom (s_of_ns (snd (f (n+q))))"
    using is_path_f' by blast
  then have "infinite (deriv (snd (f (n+q))))"
    by (simp add: Suc.prems(1) is_path_f')
  obtain xs ys where *: "snd (f (n + q)) = xs @ (0, PAtom p vs) # ys"
        "(0, PAtom p vs) \<notin> set xs"
    by (meson Prover.contains_def Suc split_list_first)
  have "(0, PAtom p vs) \<in> set (snd (f (Suc (n + q))))"
  proof (cases xs)
    case Nil
    then have "(snd (f (Suc (n + q)))) \<in> set (subs (snd (f (n + q))))"
      using Suc.prems(1) is_path_f by blast
    with * Nil show ?thesis
      by (simp split: if_splits)
  next
    case (Cons a list)
    with Suc show ?thesis 
      by (smt (verit, best) * progress append_Cons append_assoc in_set_conv_decomp)
  qed
  then show ?case
    by (simp add: contains_def)
qed 

text \<open>The same proof as above\<close>
lemma contains_propagates_natoms:
  "contains f n (0, NAtom p vs) \<Longrightarrow> contains f (n+q) (0, NAtom p vs)"
proof(induction q)
  case 0
  then show ?case
    by auto
next
  case (Suc q)
  then have \<section>: "\<not> is_axiom (s_of_ns (snd (f (n+q))))"
    using is_path_f' by blast
  then have "infinite (deriv (snd (f (n+q))))"
    by (simp add: Suc.prems(1) is_path_f')
  obtain xs ys where *: "snd (f (n + q)) = xs @ (0, NAtom p vs) # ys"
        "(0, NAtom p vs) \<notin> set xs"
    by (meson Prover.contains_def Suc split_list_first)
  have "(0, NAtom p vs) \<in> set (snd (f (Suc (n + q))))"
  proof (cases xs)
    case Nil
    then have "(snd (f (Suc (n + q)))) \<in> set (subs (snd (f (n + q))))"
      using Suc.prems(1) is_path_f by blast
    with * Nil show ?thesis
      by (simp split: if_splits)
  next
    case (Cons a list)
    with Suc show ?thesis 
      by (smt (verit, best) * progress append_Cons append_assoc in_set_conv_decomp)
  qed
  then show ?case
    by (simp add: contains_def)
qed 
    
lemma contains_propagates_fconj:
  assumes "contains f n (0, FConj g h)"
    shows "\<exists>y. contains f (n + y) (0, g) \<or> contains f (n + y) (0, h)"
proof -
  obtain l where l: "considers f (n+l) (0,FConj g h)"
    using assms contains_considers by blast
  then have *: "(snd (f (Suc (n + l)))) \<in> set (subs (snd (f (n + l))))"
    using assms(1) is_path_f by blast
  have "contains f (n + (Suc l)) (0, g) \<or> contains f (n + (Suc l)) (0, h)"
  proof (cases "snd (f (n + l))")
    case Nil
    then show ?thesis
      using considers_def l by auto
  next
    case (Cons a list)
    then show ?thesis
      using l * by (auto simp: contains_def considers_def in_set_conv_decomp)
  qed
  then show ?thesis ..
qed

lemma contains_propagates_fdisj:
  assumes "contains f n (0, FDisj g h)"
    shows "\<exists>y. contains f (n + y) (0, g) \<and> contains f (n + y) (0, h)"
proof -
  obtain l where l: "considers f (n+l) (0,FDisj g h)"
    using assms contains_considers by blast
  then obtain a list where *: "snd (f (n + l)) = a # list"
    by (metis considers_def list.simps(4) neq_Nil_conv)
  have **: "snd (f (Suc (n + l))) \<in> set (subs (snd (f (n + l))))"
    using assms is_path_f by blast
  show ?thesis
  proof (intro exI conjI)
    show "contains f (n + (Suc l)) (0, g)" "contains f (n + (Suc l)) (0, h)"
      using l * ** assms by (auto simp: contains_def considers_def in_set_conv_decomp)
  qed
qed

lemma contains_propagates_fall: 
  assumes "contains f n (0, FAll g)"
  shows "\<exists>y. contains f (Suc(n+y)) (0,finst g (newvar (sfv (s_of_ns (snd (f (n+y)))))))"
proof -
  obtain l where l: "considers f (n+l) (0, FAll g)"
    using assms contains_considers by blast
  then obtain a list where *: "snd (f (n + l)) = a # list"
    by (metis considers_def list.simps(4) neq_Nil_conv)
  have **: "snd (f (Suc (n + l))) \<in> set (subs (snd (f (n + l))))"
    using assms is_path_f by blast
  show ?thesis
  proof (intro exI conjI)
    show "contains f (Suc (n+l)) (0, finst g (newvar (sfv (s_of_ns (snd (f (n + l)))))))" 
      using l * ** assms by (auto simp: contains_def considers_def in_set_conv_decomp)
  qed
qed

lemma contains_propagates_fex: 
  assumes "contains f n (m, FEx g)"
  shows "\<exists>y. contains f (n + y) (0, finst g m) \<and> contains f (n + y) (Suc m, FEx g)"
proof -
  obtain l where l: "considers f (n+l) (m, FEx g)"
    using assms contains_considers by blast
  then obtain a list where *: "snd (f (n + l)) = a # list"
    by (metis considers_def list.simps(4) neq_Nil_conv)
  have **: "snd (f (Suc (n + l))) \<in> set (subs (snd (f (n + l))))"
    using assms is_path_f by blast
  show ?thesis
  proof (intro exI conjI)
    show "contains f (n + (Suc l)) (0, finst g m)"
         "contains f (n + (Suc l)) (Suc m, FEx g)" 
      using l * ** by (auto simp: contains_def considers_def in_set_conv_decomp)
  qed
qed
 
  \<comment> \<open>also need that if contains one, then contained an original at beginning\<close>
  \<comment> \<open>existentials: show that for exists formulae, if Suc m is marker, then there must have been m\<close>
  \<comment> \<open>show this by showing that nodes are upwardly closed, i.e. if never contains (m,x), then never contains (Suc m, x), by induction on n\<close>

lemma FEx_downward:
  assumes "init s"
  shows "(Suc m, FEx g) \<in> set (snd (f n)) \<Longrightarrow> (\<exists>n'. (m, FEx g) \<in> set (snd (f n')))"
proof (induction n arbitrary: m)
  case 0
    with inf init_def is_path_f_0 \<open>init s\<close> 
    show ?case by auto
next
  case (Suc n)
  note \<section> = Suc assms is_path_f [of "n"]
  have ?case if "f n = (n, Cons (a,fm) list)" for a fm list 
  proof (cases fm)
    case (FEx x6)
    with \<section> that show ?thesis
      by simp (metis list.set_intros(1) snd_conv)
  qed (use \<section> that in \<open>auto split: if_splits\<close>)
  then show ?case
    by (metis Suc.prems empty_iff is_path_f list.exhaust list.set(1) set_ConsD
        subs.simps(1) split_pairs)
qed
   
lemma FEx0:
  assumes "init s"
  shows "contains f n (m, FEx g) \<Longrightarrow> (\<exists>n'. contains f n' (0, FEx g))"
  using assms
  by (induction m arbitrary: n) (auto simp: contains_def dest: FEx_downward)
     
lemma FEx_upward':
  assumes "contains f n (0, FEx g)"
  shows "\<exists>n'. contains f n' (m, FEx g)"
  by (induction m; use assms contains_propagates_fex in blast)

  \<comment> \<open>FIXME contains and considers aren't buying us much\<close>
     
lemma FEx_upward: 
  assumes "init s"
    and "contains f n (m, FEx g)"
    shows "\<exists>n'. contains f n' (0, finst g m')"
proof -
  obtain n' where "contains f n' (m', FEx g)"
    using FEx0 FEx_upward' assms by blast
  then show ?thesis
    using contains_propagates_fex by blast
qed

end

subsection "Models 2"

axiomatization ntou :: "nat \<Rightarrow> U"
  where ntou: "inj ntou"  \<comment> \<open>assume universe set is infinite\<close>

definition uton :: "U \<Rightarrow> nat" where "uton = inv ntou"

lemma uton_ntou: "uton (ntou x) = x"
  by (simp add: inv_f_f ntou uton_def)

lemma map_uton_ntou[simp]: "map uton (map ntou xs) = xs"
  by (induct xs, auto simp: uton_ntou) 

lemma ntou_uton: "x \<in> range ntou \<Longrightarrow> ntou (uton x) = x"
  by (simp add: f_inv_into_f uton_def)


subsection "Falsifying Model From Failing Path"

definition model :: "nseq \<Rightarrow> model" where
  "model s \<equiv> 
    (range ntou, 
     \<lambda> p ms. let f = failing_path (deriv s) in
              \<forall>n m. \<not> contains f n (m,PAtom p (map uton ms)))"

lemma is_env_model_ntou: "is_env (model s) ntou"
  by (simp add: is_env_def model_def)

lemma (in FailingPath) [simp]: 
  "\<lbrakk>init s; contains f n (m,A); \<not> is_FEx A\<rbrakk> \<Longrightarrow> m = 0"
  by (metis Prover.contains_def index0 is_path_f' surjective_pairing)

lemma (in FailingPath) model': 
  assumes "init s"
    and A: "h = size A" "contains f n (m, A)" "FEval (model s) ntou A"
  shows "\<not> FEval (model s) ntou A"
  using A
proof (induction h arbitrary: A m n rule: less_induct)
  case (less x A m n)
  show ?case
  proof (cases A)
    case (PAtom p vs)
    then show ?thesis
      using f less.prems(2) map_uton_ntou model_def by auto
  next
    case (NAtom p vs)
    with less.prems obtain nN mN nP mP 
        where \<section>: "contains f nN (mN, NAtom p vs)" "contains f nP (mP, PAtom p vs)"
      using f  map_uton_ntou model_def by auto
    then have "mN=0" "mP=0"
      by (auto simp: inf \<open>init s\<close>)
    then obtain d where d: "considers f (nN+nP+d) (0, PAtom p vs)"
      by (metis "\<section>"(2) add.commute contains_considers contains_propagates_patoms)
    then have "is_axiom (s_of_ns (snd (f (nN+nP+d))))"
      using contains_propagates_natoms \<section> \<open>mN = 0\<close> assms
      apply (simp add: s_of_ns_def considers_def image_iff split: list.splits)
      by (metis contains_def form.distinct(1) set_ConsD snd_conv)
    then show ?thesis
      by (simp add: inf is_path_f')
  next
    case (FConj fm1 fm2)
    with less.prems inf \<open>init s\<close> have "m=0"
      by auto
    then obtain d where "contains f (n+d) (0, fm1) \<or> contains f (n+d) (0, fm2)"
      using FConj inf contains_propagates_fconj less.prems(2) by blast
    with FConj show ?thesis
      using less.IH less.prems(1) by force
  next
    case (FDisj fm1 fm2)
    with less.prems inf \<open>init s\<close> have "m=0"
      by auto
    then obtain d where "contains f (n+d) (0, fm1) \<and> contains f (n+d) (0, fm2)"
      using FDisj inf contains_propagates_fdisj less.prems(2) by blast
    with FDisj show ?thesis
      using less.IH less.prems(1) by force
  next
    case (FAll fm)
    with less.prems inf \<open>init s\<close> have "m=0"
      by auto
    then obtain d where
          "contains f (Suc (n+d)) (0, finst fm (newvar (sfv (s_of_ns (snd (f (n+d)))))))"
      using FAll inf contains_propagates_fall less.prems(2) by blast
    with FAll less have "\<not> FEval (model s) ntou (finst fm (newvar (sfv (s_of_ns (snd (f (n+d)))))))"
      by (metis add_diff_cancel_left' form.size(11) lessI size_finst zero_less_diff)
    with FAll show ?thesis
      using FEval_finst is_env_def is_env_model_ntou by auto
  next
    case (FEx fm)
    then have "\<forall>m'. \<exists>n'. contains f n' (0, finst fm m')"
      using FEx_upward assms less.prems by blast
    with FEx less have "\<forall>m'. \<not> FEval (model s) ntou (finst fm m')"
      by (metis add.comm_neutral add_Suc_right form.size(12) lessI size_finst)
    then show ?thesis
      by (simp add: FEval_finst FEx model_def)
  qed   
qed


subsection "Completeness"

\<comment> \<open>FIXME tidy deriv s so that s consists of formulae only?\<close>
lemma completeness':
  assumes "infinite (deriv s)" "init s" "(m,A) \<in> set s"
  shows "\<not> FEval (model s) ntou A"
  by (metis contains_def assms FailingPath.intro FailingPath.is_path_f_0 FailingPath.model' snd_conv)

lemma completeness: 
  assumes "infinite (deriv (ns_of_s s))"
  shows "\<not> Svalid s"
proof -
  have "init (ns_of_s s)"
    by(simp add: init_def ns_of_s_def)
  with assms have "\<And>A. A \<in> set s \<Longrightarrow> \<not> FEval (model (ns_of_s s)) ntou A"
    unfolding ns_of_s_def using completeness' by fastforce
  with assms show ?thesis
    using SEval_def2 Svalid_def is_env_model_ntou by blast
qed

subsection "Sound and Complete"

lemma "Svalid s = finite (deriv (ns_of_s s))"
  using soundness completeness by blast


subsection "Algorithm"

lemma ex_iter': "(\<exists>n. R ((g^^n)a)) = (R a \<or> (\<exists>n. R ((g^^n)(g a))))"
  by (metis (mono_tags, lifting) funpow_0 funpow_Suc_right not0_implies_Suc
      o_apply)

    \<comment> \<open>version suitable for computation\<close>
lemma ex_iter: "(\<exists>n. R ((g^^n)a)) = (if R a then True else (\<exists>n. R ((g^^n)(g a))))"
  by (metis ex_iter')

definition
  f :: "nseq list \<Rightarrow> nat \<Rightarrow> nseq list" where
  "f s n \<equiv> ((\<lambda> x. concat (map subs x))^^n) s"

lemma f_upwards: "f s n = [] \<Longrightarrow> f s (n+m) = []"
  by (induction m) (auto simp: f_def)

lemma f: "((n,x) \<in> deriv s) = (x \<in> set (f [s] n))"
unfolding f_def
proof (induction n arbitrary: x)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
    by (auto simp: deriv.simps[of "Suc n"])
qed

lemma deriv_f: "deriv s = (\<Union>x. set (map (Pair x) (f [s] x)))"
  using f by (auto simp: set_eq_iff)

lemma finite_deriv: "finite (deriv s) \<longleftrightarrow> (\<exists>m. f [s] m = [])"
proof
  assume "finite (deriv s)"
  then obtain N where m: "N \<in> fst ` deriv s" "\<forall>k. k \<in> fst ` deriv s \<longrightarrow> k \<le> N"
    by (metis deriv0 empty_iff finite_imageI image_is_empty eq_Max_iff)
  then have "f [s] (Suc N) = []"
    by (metis Suc_n_not_le_n f image_eqI list.exhaust list.set_intros(1)
        split_pairs)
  then show "\<exists>m. f [s] m = []" ..
next
  assume "\<exists>m. f [s] m = []"
  then obtain m where "f [s] m = []" ..
  then have "\<And>d. f [s] (m+d) = []"
    using f_upwards by blast
  then show "finite (deriv s)"
    by (metis empty_iff f list.set(1) FailingPath.is_path_f FailingPath_def surjective_pairing)
qed

definition prove' :: "nseq list \<Rightarrow> bool" where
  "prove' s = (\<exists>m. ((\<lambda> x. concat (map subs x))^^m) s = [])"

lemma prove': "prove' l = (if l = [] then True else prove' ((\<lambda> x. concat (map subs x)) l))"
  by (simp add: eq_Nil_null ex_iter prove'_def)
    \<comment> \<open>this is the main claim for efficiency- we have a tail recursive implementation via this lemma\<close>

definition prove :: "nseq \<Rightarrow> bool" where "prove s = prove' ([s])"

lemma finite_deriv_prove: "finite (deriv s) = prove s"
  by (simp add: finite_deriv prove_def prove'_def f_def)


subsection "Computation"

  \<comment> \<open>a sample formula to prove\<close>
lemma "(\<exists>x. A x \<or> B x) \<longrightarrow> ( (\<exists>x. B x) \<or> (\<exists>x. A x))" 
  by blast

  \<comment> \<open>convert to our form\<close>
lemma "((\<exists>x. A x \<or> B x) \<longrightarrow> ( (\<exists>x. B x) \<or> (\<exists>x. A x)))
  = ( (\<forall>x. \<not> A x \<and> \<not> B x) \<or> ( (\<exists>x. B x) \<or> (\<exists>x. A x)))" 
  by blast 

definition my_f :: "form" where
  "my_f = FDisj 
  (FAll (FConj (NAtom 0 [0]) (NAtom 1 [0])))
  (FDisj (FEx (PAtom 1 [0])) (FEx (PAtom 0 [0])))"

  \<comment> \<open>we compute by rewriting\<close>

lemma membership_simps:
  "x \<in> set [] \<longleftrightarrow> False"
  "x \<in> set (y # ys) \<longleftrightarrow> x = y \<or> x \<in> set ys"
  by simp_all

lemmas ss = list.inject if_True if_False concat.simps list.map
  sfv_def filter.simps snd_conv form.simps finst_def s_of_ns_def
  Let_def newvar_def subs.simps split_beta append_Nil append_Cons
  subst.simps nat.simps fv.simps maxvar.simps preSuc.simps simp_thms
  membership_simps

lemmas prove'_Nil = prove' [of "[]", simplified]
lemmas prove'_Cons = prove' [of "x#l", simplified] for x l

lemma search: "finite (deriv [(0,my_f)])"
  unfolding my_f_def finite_deriv_prove prove_def prove'_Nil prove'_Cons ss
  by (simp add: prove'_Nil)

abbreviation Sprove :: "form list \<Rightarrow> bool" where "Sprove \<equiv> prove \<circ> ns_of_s"

abbreviation check :: "form \<Rightarrow> bool" where "check formula \<equiv> Sprove [formula]"

abbreviation valid :: "form \<Rightarrow> bool" where "valid formula \<equiv> Svalid [formula]"

theorem "check = valid" using soundness completeness finite_deriv_prove by auto

ML \<open>

fun max x y = if x > y then x else y;

fun concat [] = []
  | concat (a::list) = a @ (concat list);

type pred = int;

type var = int;

datatype form = 
    PAtom of pred * (var list)
  | NAtom of pred * (var list)
  | FConj of form * form
  | FDisj of form * form
  | FAll  of form
  | FEx   of form;

fun preSuc [] = []
  | preSuc (a::list) = if a = 0 then preSuc list else (a-1)::(preSuc list);

fun fv (PAtom (_,vs)) = vs
  | fv (NAtom (_,vs)) = vs
  | fv (FConj (f,g)) = (fv f) @ (fv g)
  | fv (FDisj (f,g)) = (fv f) @ (fv g)
  | fv (FAll f) = preSuc (fv f)
  | fv (FEx f)  = preSuc (fv f);

fun subst r (PAtom (p,vs)) = PAtom (p,map r vs)
  | subst r (NAtom (p,vs)) = NAtom (p,map r vs)
  | subst r (FConj (f,g)) = FConj (subst r f,subst r g)
  | subst r (FDisj (f,g)) = FDisj (subst r f,subst r g)
  | subst r (FAll f) = FAll (subst (fn 0 => 0 | v => (r (v-1))+1) f)
  | subst r (FEx f)  = FEx  (subst (fn 0 => 0 | v => (r (v-1))+1) f);

fun finst body w = subst (fn 0 => w | v => v-1) body;

fun s_of_ns ns = map (fn (_,y) => y) ns;

fun ns_of_s s = map (fn y => (0,y)) s;

fun sfv s = concat (map fv s);

fun maxvar [] = 0
  | maxvar (a::list) = max a (maxvar list);

fun newvar vs = if vs = [] then 0 else (maxvar vs)+1;

fun test [] _ = false
  | test ((_,y)::list) z = if y = z then true else test list z;

fun subs [] = [[]]
  | subs (x::xs) = let val (n,f') = x in case f' of
      PAtom (p,vs) => if test xs (NAtom (p,vs)) then [] else [xs @ [(0,PAtom (p,vs))]]
    | NAtom (p,vs) => if test xs (PAtom (p,vs)) then [] else [xs @ [(0,NAtom (p,vs))]]
    | FConj (f,g) => [xs @ [(0,f)],xs @ [(0,g)]]
    | FDisj (f,g) => [xs @ [(0,f),(0,g)]]
    | FAll f => [xs @ [(0,finst f (newvar (sfv (s_of_ns (x::xs)))))]]
    | FEx f  => [xs @ [(0,finst f n),(n+1,f')]]
  end;

fun step s = concat (map subs s);

fun prove' s = if s = [] then true else prove' (step s);

fun prove s = prove' [s];

fun check f = (prove o ns_of_s) [f];

val my_f = FDisj (
  (FAll (FConj ((NAtom (0,[0])), (NAtom (1,[0])))),
  (FDisj ((FEx ((PAtom (1,[0])))), (FEx (PAtom (0,[0])))))));

check my_f;

\<close>

end
