(*  Title:       Terminated coinductive list
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Terminated coinductive lists *}

theory TLList imports
  "Quotient_Coinductive_List"
  "Quotient_Product"
  "Quotient_List"
  "Quotient_Sum"
begin

text {*
  Terminated coinductive lists @{text "('a, 'b) tllist"} are the codatatype defined by the construtors
  @{text "TNil"} of type @{text "'b \<Rightarrow> ('a, 'b) tllist"} and
  @{text "TCons"} of type @{text "'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"}.

  Instead of manually constructing @{text "('a, 'b) tllist"},
  we define it as the quotient of @{typ "'a llist \<times> 'b"} w.r.t.
  the equivalence relation that is the identity except for infinite lists @{text "xs"} 
  for which it ignores the second component.
*}

subsection {* Auxiliary lemmas *}

lemma mem_preserve [quot_preserve]: 
  assumes "Quotient R Abs Rep"
  shows "(Rep ---> (Abs ---> id) ---> id) (op \<in>) = op \<in>"
using Quotient_abs_rep[OF assms]
by(simp add: expand_fun_eq mem_def)

lemma mem_respect [quot_respect]:
  "(R ===> (R ===> op =) ===> op =) (op \<in>) (op \<in>)"
by(simp add: expand_fun_eq mem_def)

lemma sum_case_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  shows "((Abs1 ---> Rep2) ---> (Abs3 ---> Rep2) ---> sum_map Rep1 Rep3 ---> Abs2) sum_case = sum_case"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] Quotient_abs_rep[OF q3]
by(simp add: expand_fun_eq split: sum.split)

lemma sum_case_preserve2 [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "((id ---> Rep) ---> (id ---> Rep) ---> id ---> Abs) sum_case = sum_case"
using Quotient_abs_rep[OF q]
by(auto intro!: ext split: sum.split)

lemma prod_case_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  shows "((Abs1 ---> Abs2 ---> Rep3) ---> prod_fun Rep1 Rep2 ---> Abs3) prod_case = prod_case"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] Quotient_abs_rep[OF q3]
by(simp add: expand_fun_eq split: prod.split)

lemma prod_case_preserve2 [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "((id ---> id ---> Rep) ---> id ---> Abs) prod_case = prod_case"
using Quotient_abs_rep[OF q]
by(auto intro!: ext)

lemma split_fst: "R (fst p) = (\<forall>x y. p = (x, y) \<longrightarrow> R x)"
by(cases p) simp

lemma split_fst_asm: "R (fst p) \<longleftrightarrow> (\<not> (\<exists>x y. p = (x, y) \<and> \<not> R x))"
by(cases p)(simp)

subsection {* Type definition *}

fun tlist_eq :: "('a llist \<times> 'b) \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> bool"
where "tlist_eq (xs, a) (ys, b) \<longleftrightarrow> xs = ys \<and> (lfinite xs \<longrightarrow> a = b)"

lemma equivp_tlist_eq: "equivp tlist_eq"
by(rule equivpI)(auto simp add: reflp_def symp_def transp_def)

lemma sum_case_respect_tlist_eq [quot_respect]:
  "((op = ===> tlist_eq) ===> (op = ===> tlist_eq) ===> op = ===> tlist_eq) sum_case sum_case"
by(simp split: sum.split)

lemma prod_case_repsect_tlist_eq [quot_respect]:
  "((op = ===> op = ===> tlist_eq) ===> op = ===> tlist_eq) prod_case prod_case"
by(simp)


quotient_type ('a, 'b) tllist = "'a llist \<times> 'b" / tlist_eq
by(rule equivp_tlist_eq)

definition TNIL :: "'a \<Rightarrow> ('b llist \<times> 'a)"
where "TNIL = Pair LNil"

definition TCONS :: "'a \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> ('a llist \<times> 'b)"
where "TCONS = apfst \<circ> LCons"

quotient_definition "TNil :: 'a \<Rightarrow> ('b, 'a) tllist"
is "TNIL"

quotient_definition "TCons :: 'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "TCONS"

lemma TNil_respect [quot_respect]:
  "(op = ===> tlist_eq) TNIL TNIL"
by(simp add: TNIL_def)

lemma TCons_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) TCONS TCONS"
by(simp add: TCONS_def)

code_datatype TNil TCons

lemma tllist_simps [simp]:
  fixes a :: 'a and b :: 'b
  shows "TNil b \<noteq> TCons a tr"
  and "TCons a tr \<noteq> TNil b"
  and TNil_inject: "TNil b = TNil b' \<longleftrightarrow> b = b'"
  and TCons_inject: "TCons a tr = TCons a' tr' \<longleftrightarrow> a = a' \<and> tr = tr'"
proof -
  { fix a :: 'a and b :: 'b and xsb
    have "\<not> tlist_eq (TNIL b) (TCONS a xsb)"
      by(cases xsb)(simp add: TCONS_def TNIL_def) }
  note neq = this
  show "TNil b \<noteq> TCons a tr" by(lifting neq)
  thus "TCons a tr \<noteq> TNil b" by(simp)
next
  { fix b b' :: 'b
    have "tlist_eq (TNIL b) (TNIL b') \<longleftrightarrow> b = b'"
      by(simp add: TNIL_def) }
  note eqNil = this
  show "TNil b = TNil b' \<longleftrightarrow> b = b'" by(lifting eqNil)
next
  { fix a a' :: 'a and xsb xsb' :: "'a llist \<times> 'b"
    have "tlist_eq (TCONS a xsb) (TCONS a' xsb')
          \<longleftrightarrow> a = a' \<and> tlist_eq xsb xsb'"
      by(cases xsb, cases xsb')(simp add: TCONS_def) }
  note eqCons = this
  show "TCons a tr = TCons a' tr' \<longleftrightarrow> a = a' \<and> tr = tr'"
    by(lifting eqCons)
qed

primrec tllist_case_aux :: "('b \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> 'e) \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> 'e"
where "tllist_case_aux f g (xs, b) = (case xs of LNil \<Rightarrow> f b | LCons x xs' \<Rightarrow> g x (xs', b))"

lemma tllist_case_aux_respect [quot_respect]:
  "(op = ===> (op = ===> tlist_eq ===> op =) ===> tlist_eq ===> op =) tllist_case_aux tllist_case_aux"
by(auto intro: ext split: llist_split)

quotient_definition "tllist_case :: ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> ('c, 'a) tllist \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) tllist \<Rightarrow> 'b"
is "tllist_case_aux"

translations
  "case p of XCONST TNil y \<Rightarrow> a | XCONST TCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST tllist_case (\<lambda>y. a) (\<lambda>x l. b) p"

lemma tllist_case_aux_simps:
  shows tllist_case_aux_LNil: "tllist_case_aux f g (TNIL b) = f b"
  and tllist_case_aux_LCons: "tllist_case_aux f g (TCONS x xsb) = g x xsb"
by(cases xsb, simp add: split_beta TNIL_def TCONS_def)+

lemma tllist_case_TNil:
  "tllist_case f g (TNil b) = f b"
by(lifting tllist_case_aux_LNil)

lemma tllist_case_TCons:
  "tllist_case f g (TCons x tr) = g x tr"
by(lifting tllist_case_aux_LCons)

lemmas tllist_case_simps [simp, code] = 
  tllist_case_TNil tllist_case_TCons

lemma tllist_case_cert:
  assumes "CASE \<equiv> tllist_case c d"
  shows "(CASE (TNil b) \<equiv> c b) &&& (CASE (TCons M N) \<equiv> d M N)"
  using assms by simp_all

setup {*
  Code.add_case @{thm tllist_case_cert}
*}

setup {*
  Nitpick.register_codatatype @{typ "('a, 'b) tllist"} @{const_name llist_case}
    (map dest_Const [@{term TNil}, @{term TCons}])
*}

lemma tllist_exhaust_aux:
  obtains b where "xsb = TNIL b"
  | a xsb' where "xsb = TCONS a xsb'"
apply(cases xsb)
apply(rename_tac xs b)
apply(case_tac xs)
apply(fastsimp simp add: TNIL_def TCONS_def)+
done

lemma tllist_exhaust [case_names TNil TCons, cases type]:
  obtains (TNil) b where "tr = TNil b"
       | (TCons) a tr' where "tr = TCons a tr'"
by(lifting tllist_exhaust_aux)

lemma tllist_split:
  "P (tllist_case f g tr) = ((\<forall>b. tr = TNil b \<longrightarrow> P (f b)) \<and> (\<forall>a tr'. tr = TCons a tr' \<longrightarrow> P (g a tr')))"
by(cases tr) simp_all

lemma tllist_split_asm:
  "P (tllist_case f g tr) = (\<not> ((\<exists>b. tr = TNil b \<and> \<not> P (f b)) \<or> (\<exists>a tr'. tr = TCons a tr' \<and> \<not> P (g a tr'))))"
by(cases tr) simp_all

lemmas tllist_splits =
  tllist_split tllist_split_asm

subsection {* Coinduction and corecursion principles *}

lemma tlist_eq_coinduct [consumes 1, case_names tlist_eq, case_conclusion tlist_eq Nil Cons]:
  assumes major: "(xsb, xsb') \<in> r"
  and step: "\<And>q. q \<in> r \<Longrightarrow> (\<exists>b. prod_rel tlist_eq tlist_eq q (TNIL b, TNIL b)) \<or>
                           (\<exists>a xsb xsb'. prod_rel tlist_eq tlist_eq q (TCONS a xsb, TCONS a xsb') \<and> ((xsb, xsb') \<in> r \<or> tlist_eq xsb xsb'))"
  shows "tlist_eq xsb xsb'"
proof -
  obtain xs b where xsb [simp]: "xsb = (xs, b)" by(cases xsb)
  obtain xs' b' where xsb' [simp]: "xsb' = (xs', b')" by(cases xsb')
  from major have "(xs, xs') \<in> {(xs, xs'). \<exists>b b'. ((xs, b), (xs', b')) \<in> r}" by auto
  hence "xs = xs'"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs xs' b b' where q: "q = (xs, xs')"
      and r: "((xs, b), (xs', b')) \<in> r" by blast
    from step[OF r] show ?case unfolding q by(auto simp add: TCONS_def TNIL_def)
  qed
  moreover {
    assume "lfinite xs"
    hence "b = b'" using major[unfolded xsb xsb', folded `xs = xs'`]
    proof(induct)
      case lfinite_LNil
      thus ?case by(auto dest: step simp add: TNIL_def TCONS_def)
    next
      case (lfinite_LConsI xs x)
      from step[OF `((LCons x xs, b), LCons x xs, b') \<in> r`]
      have "((xs, b), (xs, b')) \<in> r \<or> tlist_eq (xs, b) (xs, b')"
        by(auto simp add: TNIL_def TCONS_def)
      thus ?case using lfinite_LConsI by(auto)
    qed }      
  ultimately show ?thesis by simp
qed

lemma tllist_equalityI [consumes 1, case_names Eqtllist, case_conclusion Eqtllist EqTNil EqTCons]:
  "\<lbrakk> (tr, tr') \<in> r;
     \<And>q. q \<in> r \<Longrightarrow> (\<exists>b. q = (TNil b, TNil b)) \<or>
                   (\<exists>a tr tr'. q = (TCons a tr, TCons a tr') \<and> ((tr, tr') \<in> r \<or> tr = tr')) \<rbrakk>
  \<Longrightarrow> tr = tr'"
by(lifting tlist_eq_coinduct)

definition tllist_corec_aux :: "'a \<Rightarrow> ('a \<Rightarrow> (('b \<times> 'a) + 'c)) \<Rightarrow> ('b llist \<times> 'c)"
where
  "tllist_corec_aux a f =
   (let f' = \<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None;
        g  = \<lambda>ac. case ac of Inl a \<Rightarrow> (case f a of Inl (b, a) \<Rightarrow> Inl a | Inr c \<Rightarrow> Inr c) | Inr c \<Rightarrow> Inr c;
        xs = llist_corec a f'
    in (xs, 
        if lfinite xs
        then THE c. (g ^^ (Suc (THE n. llength xs = Fin n))) (Inl a) = Inr c
        else undefined))"

lemma tllist_corec_aux:
  "tllist_corec_aux a f =
   (case f a of Inl (b, a') \<Rightarrow> TCONS b (tllist_corec_aux a' f)
                    | Inr c \<Rightarrow> TNIL c)"
proof(cases "lfinite (llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None))")
  case False thus ?thesis
    by(auto simp add: tllist_corec_aux_def TNIL_def TCONS_def split: sum.split)(simp_all add: llist_corec)
next
  case True
  thus ?thesis
  proof(induct xs\<equiv>"llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)" arbitrary: a)
    case lfinite_LNil[symmetric]
    thus ?case
      by(simp add: llist_corec tllist_corec_aux_def zero_inat_def TNIL_def split: sum.split_asm prod.split_asm)
  next
    case (lfinite_LConsI xs x)
    from `LCons x xs = llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)`
    obtain a' where a': "f a = Inl (x, a')"
      and xs: "xs = llist_corec a' (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)"
      by(subst (asm) (2) llist_corec)(auto split: sum.split_asm)
    from xs have "tllist_corec_aux a' f = sum_case (prod_case (\<lambda>b a'. TCONS b (tllist_corec_aux a' f))) TNIL (f a')"
      by(rule lfinite_LConsI)
    thus ?case using `lfinite xs` a' xs
      by(auto simp add: tllist_corec_aux_def TCONS_def TNIL_def Let_def iSuc_Fin funpow_Suc_tail_rec llist_corec dest!: lfinite_llength_Fin simp del: funpow.simps)
  qed
qed

quotient_definition "tllist_corec :: 'a \<Rightarrow> ('a \<Rightarrow> (('b \<times> 'a) + 'c)) \<Rightarrow> ('b, 'c) tllist"
is "tllist_corec_aux"

lemma tllist_corec_aux_respect_tlist_eq [quot_respect]:
  "(op = ===> op = ===> tlist_eq) tllist_corec_aux tllist_corec_aux"
by(auto intro: ext equivp_reflp[OF tllist_equivp])

lemma tllist_corec [code, nitpick_simp]:
  "tllist_corec a f = (sum_case (prod_case (\<lambda>b a'. TCons b (tllist_corec a' f))) TNil (f a))"
by(lifting tllist_corec_aux)

subsection {* Lifting constants from @{typ "'a llist"} to @{typ "('a, 'b) tllist"} *}

primrec tMAP :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a llist \<times> 'c \<Rightarrow> 'b llist \<times> 'd"
where "tMAP f g (xs, b) = (lmap f xs, g b)"

quotient_definition "tmap :: ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) tllist \<Rightarrow> ('b, 'd) tllist"
is "tMAP"

lemma tMAP_respect [quot_respect]:
  "(op = ===> op = ===> tlist_eq ===> tlist_eq) tMAP tMAP"
by(auto intro: ext)

lemma tMAP_TNIL: "tMAP f g (TNIL b) = TNIL (g b)"
by(simp add: TNIL_def)

lemma tmap_TNil [simp, code]: "tmap f g (TNil b) = TNil (g b)"
by(lifting tMAP_TNIL)

lemma tMAP_TCONS: "tMAP f g (TCONS a xsb) = TCONS (f a) (tMAP f g xsb)"
by(cases xsb)(simp add: TCONS_def)

lemma tmap_TCons [simp, code]: "tmap f g (TCons a tr) = TCons (f a) (tmap f g tr)"
by(lifting tMAP_TCONS)

primrec tAPPEND :: "'a llist \<times> 'b \<Rightarrow> ('b \<Rightarrow> 'a llist \<times> 'c) \<Rightarrow> 'a llist \<times> 'c"
where "tAPPEND (xs, b) f = (lappend xs (fst (f b)), snd (f b))"

quotient_definition "tappend :: ('a, 'b) tllist \<Rightarrow> ('b \<Rightarrow> ('a, 'c) tllist) \<Rightarrow> ('a, 'c) tllist"
is "tAPPEND"

lemma tappend_respect [quot_respect]:
  "(tlist_eq ===> (op = ===> tlist_eq) ===> tlist_eq) tAPPEND tAPPEND"
apply(auto intro: ext simp add: lappend_inf split: split_fst)
apply(erule_tac x=ba in allE, auto)+
done

lemma tAPPEND_TNIL: "tAPPEND (TNIL b) f = f b"
by(simp add: TNIL_def)

lemma tappend_TNil [simp, code]: "tappend (TNil b) f = f b"
by(lifting tAPPEND_TNIL)

lemma tAPPEND_TCONS: "tAPPEND (TCONS a xsb) f = TCONS a (tAPPEND xsb f)"
by(cases xsb)(simp add: TCONS_def)

lemma tappend_TCons [simp, code]: "tappend (TCons a tr) f = TCons a (tappend tr f)"
by(lifting tAPPEND_TCONS)

primrec lAPPENDt :: "'a llist \<Rightarrow> 'a llist \<times> 'b \<Rightarrow> 'a llist \<times> 'b"
where "lAPPENDt xs (ys, b) = (lappend xs ys, b)"

quotient_definition "lappendt :: 'a llist \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "lAPPENDt"

lemma lappendt_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) lAPPENDt lAPPENDt"
by(auto intro: ext)

lemma lAPPENDt_LNil: "lAPPENDt LNil xsb = xsb"
by(cases xsb) simp

lemma lappendt_LNil [simp, code]: "lappendt LNil tr = tr"
by(lifting lAPPENDt_LNil)

lemma lAPPENDt_LCons: "lAPPENDt (LCons x xs) xsb = TCONS x (lAPPENDt xs xsb)"
by(cases xsb)(simp add: TCONS_def)

lemma lappendt_LCons [simp, code]: "lappendt (LCons x xs) tr = TCons x (lappendt xs tr)"
by(lifting lAPPENDt_LCons)

primrec tFILTER :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b llist \<times> 'a) \<Rightarrow> ('b llist \<times> 'a)"
where "tFILTER b P (xs, b') = (lfilter P xs, if lfinite xs then b' else b)"

quotient_definition "tfilter :: 'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b, 'a) tllist \<Rightarrow> ('b, 'a) tllist"
is "tFILTER"

lemma tfilter_respect [quot_respect]: 
  "(op = ===> op = ===> tlist_eq ===> tlist_eq) tFILTER tFILTER"
by(auto intro: ext)

lemma tFILTER_TNIL: "tFILTER b' P (TNIL b) = TNIL b"
by(simp add: TNIL_def)

lemma tfilter_TNil [code, simp]:
  "tfilter b' P (TNil b) = TNil b"
by(lifting tFILTER_TNIL)

lemma tFILTER_TCONS: "tFILTER b P (TCONS a xsb) = (if P a then TCONS a (tFILTER b P xsb) else tFILTER b P xsb)"
by(cases xsb)(simp add: TCONS_def)

lemma tfilter_TCons [code, simp]:
  "tfilter b P (TCons a tr) = (if P a then TCons a (tfilter b P tr) else tfilter b P tr)"
by(lifting tFILTER_TCONS)

primrec tCONCAT :: "'a \<Rightarrow> ('b llist llist \<times> 'a) \<Rightarrow> ('b llist \<times> 'a)"
where "tCONCAT b (xss, b') = (lconcat xss, if lfinite xss then b' else b)"

quotient_definition "tconcat :: 'a \<Rightarrow> ('b llist, 'a) tllist \<Rightarrow> ('b, 'a) tllist"
is "tCONCAT"

lemma tconcat_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) tCONCAT tCONCAT"
by(auto intro: ext)

lemma tCONCAT_TNIL: "tCONCAT b (TNIL b') = TNIL b'"
by(simp add: TNIL_def)

lemma tconcat_TNil [code, simp]: "tconcat b (TNil b') = TNil b'"
by(lifting tCONCAT_TNIL)

lemma tCONCAT_TCONS: "tCONCAT b (TCONS a xsb) = lAPPENDt a (tCONCAT b xsb)"
by(cases xsb)(simp add: TCONS_def)

lemma tconcat_TCons [code, simp]: "tconcat b (TCons a tr) = lappendt a (tconcat b tr)"
by(lifting tCONCAT_TCONS)

end