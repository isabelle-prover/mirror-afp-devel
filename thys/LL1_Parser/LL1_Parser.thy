section \<open>Parser\<close>

theory LL1_Parser
  imports Parse_Table
begin


datatype ('n, 't) parse_tree = Node "'n" "('n, 't) parse_tree list" | Leaf "'t"

datatype ('n, 't, 's) return_type = RESULT "('n, 't \<times> 's) parse_tree" "('t \<times> 's) list"
  | ERROR "string" "'n" "('t \<times> 's) list"
  | GRAMMAR_NOT_LL1 "string" "'t lookahead"
  | REJECT "string" "('t \<times> 's) list"

fun peek :: "('t \<times> 's) list \<Rightarrow> 't lookahead" where
  "peek [] = EOF"
| "peek (t#ts) = LA (fst t)"


locale parse =
  fixes showT :: "'t \<Rightarrow> string" and showS :: "'s \<Rightarrow> string"
begin

definition mismatchMessage :: "'t \<Rightarrow> 't \<times> 's \<Rightarrow> string" where
  "mismatchMessage a \<equiv> \<lambda>(a', s).
  ''Token mismatch. Expected '' @ showT a @ '', saw '' @ showT a' @ '' ('' @ showS s @ '')''"

function (domintros) parseSymbol ::
  "('n, 't) parse_table \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('t \<times> 's) list \<Rightarrow> 'n fset \<Rightarrow> ('n, 't, 's) return_type"
and
  parseGamma ::
  "('n, 't) parse_table \<Rightarrow> 'n \<Rightarrow> ('n, 't) symbol list \<Rightarrow> ('t \<times> 's) list \<Rightarrow> 'n fset
  \<Rightarrow> ('n, 't, 's) return_type"
  where
    "parseSymbol _ (T a) [] _ = REJECT ''input exhausted'' []"
  | "parseSymbol pt (T a) (t#ts) vis = (if fst t = a then RESULT (Leaf t) ts
    else REJECT (mismatchMessage a t) (t#ts))"
  | "parseSymbol pt (NT x) ts vis = (if x |\<in>| vis then ERROR ''left recursion detected'' x ts
    else (case fmlookup pt (x, peek ts) of
      None \<Rightarrow> REJECT ''lookup failure'' ts
    | Some (x', gamma) \<Rightarrow> (if x \<noteq> x' then ERROR ''malformed parse table'' x ts
        else parseGamma pt x gamma ts (finsert x vis))
    ))"
  | "parseGamma pt n [] ts vis = RESULT (Node n []) ts"
  | "parseGamma pt n (s#gamma') ts vis = (let parse_s = parseSymbol pt s ts vis in
    (case parse_s of
      RESULT t r \<Rightarrow>
        (let parse_g = parseGamma pt n gamma' r (if length r < length ts then {||} else vis) in
          (case parse_g of
            RESULT (Node n tls) r' \<Rightarrow> RESULT (Node n (t # tls)) r'
          | e \<Rightarrow> e))
    | e \<Rightarrow> e))"
proof (goal_cases)
  case (1 P x)
  show ?case
  proof (cases x)
    case (Inl a)
    then show ?thesis
    proof (cases a)
      case (fields t u v w)
      then show ?thesis using "1" Inl by (cases u; cases v) auto
    qed
  next
    case (Inr b)
    then show ?thesis
    proof (cases b)
      case (fields t u v w)
      then show ?thesis using "1" Inr by (cases v) auto
    qed
  qed
qed auto

definition nt_from_pt :: "('n, 't) parse_table \<Rightarrow> 'n fset" where
  "nt_from_pt pt = fst |`| fmdom pt"

definition parse_ind_meas_sym ::
  "('n, 't) parse_table \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('t \<times> 's) list \<Rightarrow> 'n fset \<Rightarrow> nat \<times> nat \<times> nat" where
  "parse_ind_meas_sym pt s ts vis =  (length ts, fcard (nt_from_pt pt |-| vis), 0)"

definition parse_ind_meas_sym_list ::
  "('n, 't) parse_table \<Rightarrow> ('n, 't) symbol list \<Rightarrow> ('t \<times> 's) list \<Rightarrow> 'n fset \<Rightarrow> nat \<times> nat \<times> nat"
where
  "parse_ind_meas_sym_list pt ss ts vis = (length ts, fcard (nt_from_pt pt |-| vis), length ss + 1)"

definition parse_ind_meas :: "('n, 't) parse_table \<Rightarrow> ('n, 't) symbol + ('n, 't) symbol list \<Rightarrow>
    ('t \<times> 's) list \<Rightarrow> 'n fset \<Rightarrow> nat \<times> nat \<times> nat" where
  "parse_ind_meas pt ss ts vis = (length ts, fcard (nt_from_pt pt |-| vis),
    (case ss of Inl ss' \<Rightarrow> 0 | Inr ss' \<Rightarrow> length ss' + 1))"

definition lex_triple ::
  "('a \<times> 'a) set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('c \<times> 'c) set \<Rightarrow> (('a \<times> 'b \<times> 'c) \<times> ('a \<times> 'b \<times> 'c)) set"
  where "lex_triple ra rb rc = ra <*lex*> (rb <*lex*> rc)"

lemma in_lex_triple[simp]: "((a, b, c), (a', b', c')) \<in> lex_triple r s t
    \<longleftrightarrow> (a, a') \<in> r \<or> a = a' \<and> (b, b') \<in> s \<or> a = a' \<and> b = b' \<and> (c, c') \<in> t"
  by (auto simp:lex_triple_def)

lemma wf_lex_triple[intro!]:
  assumes "wf ra" "wf rb" "wf rc"
  shows "wf (lex_triple ra rb rc)"
  by (simp add: assms parse.lex_triple_def wf_lex_prod)

definition mlex_triple :: "('a \<Rightarrow> nat \<times> nat \<times> nat) \<Rightarrow> ('a \<times> 'a) set" where
  "mlex_triple f = inv_image (lex_triple less_than less_than less_than) f"

lemma parseSymbol_length_bound_partial:
  "parseSymbol_parseGamma_dom (Inl (pt, s, ts, vis))
  \<Longrightarrow> (\<And>tr r. parseSymbol pt s ts vis = RESULT tr r \<Longrightarrow> length r \<le> length ts)" and
  parseGamma_length_bound_partial:
  "parseSymbol_parseGamma_dom (Inr (pt, n, gamma, ts, vis))
  \<Longrightarrow> (\<And>tr r. parseGamma pt n gamma ts vis = RESULT tr r \<Longrightarrow> length r \<le> length ts)"
proof (induction rule: parseSymbol_parseGamma.pinduct)
  case (1 pt a vis)
  then show ?case
    by (simp add: parseSymbol.psimps(1))
next
  case (2 pt a t ts vis)
  then show ?case
    by (simp add: parseSymbol.psimps(2) split: if_splits)
next
  case (3 pt x ts vis)
  then show ?case by (auto simp add: parseSymbol.psimps(3) split: if_splits option.splits)
next
  case (4 pt n ts vis)
  then show ?case by (auto simp add: parseGamma.psimps(1))
next
  case (5 pt n s gamma' ts vis)
  then show ?case
    by (fastforce simp add: parseGamma.psimps(2) split: return_type.splits parse_tree.splits)
qed

lemma fcard_diff_insert_less:
  assumes "x |\<notin>| vis" "fmlookup pt (x,peek ts) = Some (x,ss)"
  shows "fcard (nt_from_pt pt - (finsert x vis)) < fcard (nt_from_pt pt - vis)"
proof -
  from assms(2) have "x |\<in>| nt_from_pt pt" by (metis fimage_eqI fmdomI fst_conv nt_from_pt_def)
  then have "x |\<in>| nt_from_pt pt - vis" using assms(1) by simp
  then show ?thesis by (metis fcard_fminus1_less fminus_finsert)
qed

termination
proof (relation "mlex_triple (\<lambda>x. case x of
      Inl (pt, s, ts, vis) \<Rightarrow> parse_ind_meas_sym pt s ts vis
    | Inr (pt, n, ss, ts, vis) \<Rightarrow> parse_ind_meas_sym_list pt ss ts vis)", goal_cases)
  case 1
  then show ?case by (simp add: mlex_triple_def wf_lex_triple)
next
  case (2 pt x ts vis s x' gamma)
  have "fcard (nt_from_pt pt - (finsert x vis)) < fcard (nt_from_pt pt - vis)"
    using "2" fcard_diff_insert_less by fastforce
  then show ?case unfolding mlex_triple_def parse_ind_meas_sym_list_def parse_ind_meas_sym_def by
      auto
next
  case (3 pt s gamma' ts vis)
  then show ?case unfolding mlex_triple_def parse_ind_meas_sym_list_def parse_ind_meas_sym_def by
      auto
next
  case (4 pt s gamma' ts vis y z str r)
  then show ?case unfolding mlex_triple_def parse_ind_meas_sym_list_def parse_ind_meas_sym_def
    by (fastforce dest: parseSymbol_length_bound_partial)
qed

fun parse ::
  "('n, 't) ll1_parse_table \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('t \<times> 's) list \<Rightarrow> ('n, 't, 's) return_type"
where
  "parse (PT pt) s ts = parseSymbol pt s ts {||}"
| "parse (ERROR_GRAMMAR_NOT_LL1_AMB_LA l) s ts =
    (case l of (a, p1, p) \<Rightarrow> GRAMMAR_NOT_LL1 ''Grammar not LL1, ambigous lookahead '' a)"

fun concatWithSep :: "string \<Rightarrow> string \<Rightarrow> string" where
  "concatWithSep [] [] = []"
| "concatWithSep [] acc = acc"
| "concatWithSep s [] = s"
| "concatWithSep s (c # acc) = (if c = CHR '' '' then s @ c # acc else s @ '' '' @ c # acc)"

fun parseTreeToString :: "('n, 't \<times> 's) parse_tree \<Rightarrow> string" where
  "parseTreeToString (Leaf (a, s)) = ''('' @ showT a @ '', '' @ showS s @ '')''"
| "parseTreeToString (Node n ls) = foldr concatWithSep (map parseTreeToString ls) ''''"

fun parseToString ::
  "('n, 't) ll1_parse_table \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('t \<times> 's) list \<Rightarrow> string" where
  "parseToString (PT pt) s ts = (case parseSymbol pt s ts {||} of
    RESULT t [] \<Rightarrow> parseTreeToString t)"
| "parseToString (ERROR_GRAMMAR_NOT_LL1_AMB_LA l) s ts = ''Grammar not LL1, ambigous lookahead '' @
    (case l of (a, p1, p) \<Rightarrow> (case a of LA t \<Rightarrow> showT t | EOF \<Rightarrow> ''EOF''))"

subsection \<open>Soundness\<close>

inductive sym_derives_prefix ::
  "('n, 't) grammar \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('t \<times> 's) list
  \<Rightarrow> ('n, 't \<times> 's) parse_tree \<Rightarrow> ('t \<times> 's) list \<Rightarrow> bool"
  and gamma_derives_prefix :: "('n, 't) grammar \<Rightarrow> 'n \<Rightarrow> ('n, 't) symbol list \<Rightarrow> ('t \<times> 's) list
    \<Rightarrow> ('n, 't \<times> 's) parse_tree \<Rightarrow> ('t \<times> 's) list \<Rightarrow> bool" for g
where
  T_sdp: "sym_derives_prefix g (T a) [(a, s)] (Leaf (a, s)) r"
| NT_sdp: "(x, gamma) \<in> set (prods g) \<Longrightarrow> lookahead_for (peek (w @ r)) x gamma g
    \<Longrightarrow> gamma_derives_prefix g x gamma w t r \<Longrightarrow> sym_derives_prefix g (NT x) w t r"
| Nil_gdp: "gamma_derives_prefix g x [] [] (Node x []) r"
| Cons_gdp: "sym_derives_prefix g s wpre v (wsuf @ r)
    \<Longrightarrow> gamma_derives_prefix g n ss wsuf (Node n vs) r
    \<Longrightarrow> gamma_derives_prefix g n (s#ss) (wpre @ wsuf) (Node n (v # vs)) r"

lemma parseSymbol_ts_contains_remainder:
  "\<And>t r. parseSymbol pt s ts vis = RESULT t r \<Longrightarrow> \<exists>ts'. ts' @ r = ts" and
  parseGamma_ts_contains_remainder:
  "\<And>t r. parseGamma pt n gamma ts vis = RESULT t r \<Longrightarrow> \<exists>ts'. ts' @ r = ts"
proof (induction pt s ts vis and pt n gamma ts vis rule: parseSymbol_parseGamma.induct)
  case (5 pt n s gamma' ts vis)
  then show ?case by (fastforce split: return_type.splits parse_tree.splits option.splits if_splits)
qed (auto split: return_type.splits parse_tree.splits option.splits if_splits)

lemma parse_meas_induct:
  assumes "\<And>y. (\<And>x. ((x,y) \<in> mlex_triple (\<lambda>x. case x of
      Inl (pt, s, ts, vis) \<Rightarrow> parse_ind_meas_sym pt s ts vis
    | Inr (pt, x, ss, ts, vis) \<Rightarrow> parse_ind_meas_sym_list pt ss ts vis) \<Longrightarrow> P x)) \<Longrightarrow> P y"
  shows "P z"
  using assms
  by (auto intro: wf_induct_rule[where r = "mlex_triple (\<lambda>x. case x of
      Inl (pt, s, ts, vis) \<Rightarrow> parse_ind_meas_sym pt s ts vis
    | Inr (pt, x, ss, ts, vis) \<Rightarrow> parse_ind_meas_sym_list pt ss ts vis)"]
        simp add: mlex_triple_def wf_lex_triple)

lemma parseGamma_node: "parseSymbol pt s ts vis = RESULT v r \<Longrightarrow> True"
  "parseGamma pt x gamma ts vis = RESULT v r \<Longrightarrow> \<exists>ls. v = Node x ls"
proof (induction pt s ts vis and pt x gamma ts vis arbitrary: and v r
    rule: parseSymbol_parseGamma.induct)
  case (5 pt n s' gamma' ts vis)
  obtain a b where A: "parseSymbol pt s' ts vis = RESULT a b"
    using 5(2,3) by (auto split: return_type.splits parse_tree.splits if_splits)
  show ?case
  proof (cases gamma')
    case Nil
    then have "parseGamma pt n gamma' b (if length b < length ts then {||} else vis)
        = RESULT (Node n []) b"
      by auto
    then show ?thesis using 5(3) A
      by (auto split: return_type.splits parse_tree.splits)
  next
    case (Cons x'' gamma'')
    obtain ls where "v = Node n ls" using 5(2,3) A by
        (auto split: return_type.splits parse_tree.splits)
    then show ?thesis by auto
  qed
qed auto

lemma parseSymbol_parseGamma_sound: "case x of Inl (pt, s, ts, vis) \<Rightarrow> parse_table_correct pt g
  \<longrightarrow> parseSymbol pt s ts vis = RESULT v r \<longrightarrow> (\<exists>w. w @ r = ts \<and> sym_derives_prefix g s w v r)
  | Inr (pt, n, gamma, ts, vis) \<Rightarrow> parse_table_correct pt g
  \<longrightarrow> (parseGamma pt n gamma ts vis = RESULT v r
  \<longrightarrow> (\<exists>w. w @ r = ts \<and> gamma_derives_prefix g n gamma w v r))"
proof (induction arbitrary: v r rule: parse_meas_induct)
  case (1 y)
  note IH = "1"
  {
    fix pt s ts vis
    assume A: "y = Inl (pt, s, ts, vis)" "parse_table_correct pt g"
        "parseSymbol pt s ts vis = RESULT v r"
    consider (T) a lex ts' where "s = T a" "ts = (a,lex)#ts'" "v = Leaf (a, lex)" "r = ts'"
      | (NT) x ss where "s = NT x" "x |\<notin>| vis" "fmlookup pt (x, peek ts) = Some (x, ss)"
        "parseSymbol pt s ts vis = parseGamma pt x ss ts (finsert x vis)"
      using A(3) by (cases s; cases ts) (auto split: if_splits option.splits)
    then have "\<exists>w. w @ r = ts \<and> sym_derives_prefix g s w v r"
    proof cases
      case T
      then show ?thesis by (auto simp add: T_sdp)
    next
      case NT
      then have "(Inr (pt, x, ss, ts, (finsert x vis)), y) \<in> mlex_triple
        (\<lambda>x. case x of Inl (pt, s, ts, vis) \<Rightarrow> parse_ind_meas_sym pt s ts vis
         | Inr (pt, x, ss, ts, vis) \<Rightarrow> parse_ind_meas_sym_list pt ss ts vis)"
        unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
        using A(1) fcard_diff_insert_less by simp
      then obtain w where " w @ r = ts" "gamma_derives_prefix g x ss w v r"
        using IH[of "Inr (pt, x, ss, ts, (finsert x vis))"] A NT by auto
      then show ?thesis using A(2) NT(1,3) NT_sdp pt_sound_def by fastforce
    qed
  }
  note 1 = this
  {
    fix pt x ss ts vis
    assume A: "y = Inr (pt, x, ss, ts, vis)" "parse_table_correct pt g"
        "parseGamma pt x ss ts vis = RESULT v r"
    consider (Nil) "ss = []"
      | (ConsLe) s ss' t tls r1 where "ss = s#ss'"
        "parseSymbol pt s ts vis = RESULT t r1" "length r1 < length ts"
        "parseGamma pt x ss' r1 {||} = RESULT (Node x tls) r" "v = Node x (t # tls)"
      | (ConsEq) s ss' t tls where "ss = s#ss'" "parseSymbol pt s ts vis = RESULT t ts"
        "parseGamma pt x ss' ts vis = RESULT (Node x tls) r" "v = Node x (t # tls)"
    proof (cases ss)
      case Nil
      then show ?thesis by (simp add: that(1))
    next
      case (Cons s ss')
      then show ?thesis
        using parseSymbol_ts_contains_remainder parseGamma_node(2) A(3)
        by (fastforce simp: ConsLe ConsEq split: return_type.splits if_splits)
    qed
    then have "\<exists>w. w @ r = ts \<and> gamma_derives_prefix g x ss w v r"
    proof (cases)
      case Nil
      then show ?thesis using A(3) Nil_gdp by auto
    next
      case ConsLe
      obtain wpre wsuf where "ts = wpre @ wsuf @ r" "wsuf @ r = r1"
        using parseGamma_ts_contains_remainder A(3) parseSymbol_ts_contains_remainder ConsLe(2,4)
        by metis
      then have "gamma_derives_prefix g x ss' wsuf (Node x tls) r"
        using IH[of "Inr (pt, x, ss', r1, {||})"] A(1,2) ConsLe(3,4)
        unfolding mlex_triple_def parse_ind_meas_sym_list_def
        by (auto simp add: A(1))
      moreover have "sym_derives_prefix g s wpre t (wsuf @ r)"
        using IH[of "Inl (pt, s, ts, vis)"] \<open>ts = wpre @ wsuf @ r\<close> \<open>wsuf @ r = r1\<close> A ConsLe(2)
        unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
        by (auto simp add: A(1))
      ultimately show ?thesis by (simp add: ConsLe(1,5) Cons_gdp \<open>ts = wpre @ wsuf @ r\<close>)
    next
      case ConsEq
      obtain w where "ts = w @ r" using ConsEq(3) parseGamma_ts_contains_remainder by
          fastforce
      have "length ss' < length ss" by (cases w) (auto simp add: \<open>ts = w @ r\<close> ConsEq(1))
      then have "gamma_derives_prefix g x ss' w (Node x tls) r"
        using IH[of "Inr (pt, x, ss', ts, vis)"] A(1,2) ConsEq(3)
        unfolding mlex_triple_def parse_ind_meas_sym_list_def
        by (auto simp add: A(1) \<open>ts = w @ r\<close>)
      moreover have "sym_derives_prefix g s [] t ts"
        using IH[of "Inl (pt, s, ts, vis)"] \<open>ts = w @ r\<close> A ConsEq(2)
        unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
        by (auto simp add: A(1))
      ultimately show ?thesis using ConsEq(1,4) Cons_gdp \<open>ts = w @ r\<close> by fastforce
    qed
  }
  note 2 = this
  then show ?case using 1 2 by (cases y) (auto split: prod.splits)
qed

theorem parse_sound: "parse_table_correct pt g \<Longrightarrow> parse (PT pt) s (w @ r) = RESULT v r
  \<Longrightarrow> sym_derives_prefix g s w v r"
  using parseSymbol_parseGamma_sound[where x = "Inl (pt, s, (w @ r), {||})"]
  by auto


subsection "Completeness"

lemma parseSymbol_parseGamma_complete_or_error:
  assumes "parse_table_correct pt g"
  shows "sym_derives_prefix g s w v r
    \<Longrightarrow> (\<forall>vis. (\<exists>m x ts'. parseSymbol pt s (w @ r) vis = ERROR m x ts')
    \<or> (parseSymbol pt s (w @ r) vis = RESULT v r))"
    and "gamma_derives_prefix g y ss w v r
     \<Longrightarrow> (\<forall>vis. (\<exists>m x ts'. parseGamma pt y ss (w @ r) vis = ERROR m x ts')
    \<or> (parseGamma pt y ss (w @ r) vis = RESULT v r))"
proof (induction rule: sym_derives_prefix_gamma_derives_prefix.inducts)
  case (T_sdp a r)
  then show ?case by auto
next
  case (NT_sdp x gamma w r v)
  have "fmlookup pt (x,peek (w @ r)) = Some (x, gamma)"
    using NT_sdp.IH(1) NT_sdp.IH(2) assms pt_complete_def by fastforce
  then have "(\<exists>m y ts'. parseSymbol pt (NT x) (w @ r) vis = ERROR m y ts')
    \<or> parseSymbol pt (NT x) (w @ r) vis = RESULT v r" for vis
  proof (cases "x |\<in>| vis")
    case True
    then show ?thesis by simp
  next
    case False
    then have "parseSymbol pt (NT x) (w @ r) vis = parseGamma pt x gamma (w @ r) (finsert x vis)"
      using \<open>fmlookup pt (x, peek (w @ r)) = Some (x, gamma)\<close> by auto
    then show ?thesis using NT_sdp.IH(4) by auto
  qed
  then show ?case by auto
next
  case (Nil_gdp r)
  then show ?case by auto
next
  case (Cons_gdp s wpre v wsuf r n ss vs)
  then have "(\<exists>m x ts'. parseGamma pt n (s # ss) ((wpre @ wsuf) @ r) vis = ERROR m x ts')
    \<or> parseGamma pt n (s # ss) ((wpre @ wsuf) @ r) vis = RESULT (Node n (v # vs)) r" for vis
  proof -
    have "\<exists>m x ts'. parseSymbol pt s (wpre @ wsuf @ r) vis = ERROR m x ts'
      \<or> parseSymbol pt s (wpre @ wsuf @ r) vis = RESULT v (wsuf @ r)" using Cons_gdp.IH(2) by auto
    moreover have "\<exists>m x ts'. parseGamma pt n ss (wsuf @ r) vis = ERROR m x ts'
      \<or> parseGamma pt n ss (wsuf @ r) vis = RESULT (Node n vs) r" using Cons_gdp(4) by auto
    moreover have "\<exists>m x ts'. parseGamma pt n ss (wsuf @ r) {||} = ERROR m x ts'
      \<or> parseGamma pt n ss (wsuf @ r) {||} = RESULT (Node n vs) r" using Cons_gdp(4) by auto
    ultimately show ?thesis by (cases "parseSymbol pt s (wpre @ wsuf @ r) vis") auto
  qed
  then show ?case by auto
qed

lemma parse_complete_or_error: "parse_table_correct pt g \<Longrightarrow> sym_derives_prefix g s w v r
  \<Longrightarrow> \<exists>m x ts'. parse (PT pt) s (w @ r) = ERROR m x ts'
  \<or> (parse (PT pt) s (w @ r) = RESULT v r)"
  using parseSymbol_parseGamma_complete_or_error by fastforce


subsection \<open>Error-free Termination\<close>

inductive sized_first_sym :: "('n, 't) grammar \<Rightarrow> 't lookahead \<Rightarrow> ('n, 't) symbol \<Rightarrow> nat \<Rightarrow> bool"
  for g where
    SzFirstT: "sized_first_sym g (LA y) (T y) 0"
  | SzFirstNT: "(x, gpre @ s # gsuf) \<in> set (prods g) \<Longrightarrow> nullable_gamma g gpre
    \<Longrightarrow> sized_first_sym g la s n \<Longrightarrow> sized_first_sym g la (NT x) (Suc n)"

lemma first_sym_exists_size: "first_sym g la s \<Longrightarrow> \<exists>n. sized_first_sym g la s n"
  using SzFirstT SzFirstNT
  by -(induction rule: first_sym.induct; fastforce)

lemma sized_fs_fs: "sized_first_sym g la s n \<Longrightarrow> first_sym g la s"
  by (induction rule: sized_first_sym.induct) (auto simp add: FirstT FirstNT)

lemma medial : "pre @ s # suf = pre' @ s' # suf'
    \<Longrightarrow> s \<in> set pre'\<or> s' \<in> set pre \<or> pre = pre' \<and> s = s' \<and> suf = suf'"
proof (induction pre arbitrary: pre')
  case Nil
  then show ?case by (cases pre') auto
next
  case (Cons a pre)
  then show ?case by (cases pre') auto
qed

lemma nullable_sym_in: "nullable_gamma g gamma \<Longrightarrow> s \<in> set gamma \<Longrightarrow> nullable_sym g s"
proof (induction gamma)
  case (Cons s' gamma)
  have "nullable_gamma g gamma" using Cons.prems(1) by (cases rule: nullable_gamma.cases)
  moreover have "nullable_sym g s'" using Cons.prems(1) by (cases rule: nullable_gamma.cases)
  ultimately show ?case using Cons.IH Cons.prems(2) by (cases "s = s'") auto
qed simp

lemma nullable_split: "nullable_gamma g (xs @ ys) \<Longrightarrow> nullable_gamma g ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons s xs)
  from Cons.prems have "nullable_gamma g (xs @ ys)" by (cases rule: nullable_gamma.cases) auto
  then show ?case using Cons.IH by auto
qed

lemma first_gamma_split:
  "first_gamma g la ys \<Longrightarrow> nullable_gamma g xs \<Longrightarrow> first_gamma g la (xs @ ys)"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons s xs)
  from Cons.prems(2) have "nullable_gamma g xs" by (cases) auto
  then have "first_gamma g la (xs @ ys)" using Cons.IH Cons.prems(1) by auto
  then obtain xs' s' ys' where "first_sym g la s'" "nullable_gamma g xs'" "xs @ ys = xs' @ s' # ys'"
    by (cases rule: first_gamma.cases) auto
  have "nullable_sym g s" using Cons.prems(2) by (cases) auto
  then have "nullable_gamma g (s # xs')" by (simp add: NullableCons \<open>nullable_gamma g xs'\<close>)
  then show ?case using FirstGamma[where gpre = "s # xs'" and s = s' and gsuf = "ys'"] by
      (simp add: \<open>first_sym g la s'\<close> \<open>xs @ ys = xs' @ s' # ys'\<close>)
qed

lemma follow_pre: "(x, pre @ suf) \<in> set (prods g) \<Longrightarrow> s \<in> set pre \<Longrightarrow> nullable_gamma g pre
  \<Longrightarrow> first_gamma g la suf \<Longrightarrow> follow_sym g la s"
proof goal_cases
  case 1
  then obtain l1 l2 where l1_l2_def: "pre = l1 @ s # l2" by (metis split_list)
  then show ?case
  proof (cases s)
    case (NT x)
    have "nullable_gamma g (l1 @ NT x # l2)" using "1"(3) by (auto simp add: l1_l2_def NT)
    then have "nullable_gamma g l2" using nullable_split[where xs = "l1 @ [NT x]"] by auto
    then have "first_gamma g la (l2 @ suf)" by (simp add: "1"(4) first_gamma_split)
    then show ?thesis using FollowRight[where gsuf = "l2 @ suf"] NT "1"(1) l1_l2_def by auto
  next
    case (T t)
    then show ?thesis using "1"(2,3) nullable_sym.cases nullable_sym_in by blast
  qed
qed

lemma no_first_follow_conflicts:
  assumes "parse_table_correct tbl g"
  shows "first_sym g la s \<Longrightarrow> nullable_sym g s \<Longrightarrow> \<not> follow_sym g la s"
  unfolding not_def
proof (intro impI, induction rule: first_sym.induct)
  case (FirstT y)
  then show ?case by (cases rule: nullable_sym.cases)
next
  case (FirstNT x gpre s gsuf la)
  from FirstNT.prems(1) obtain ys where ys_props: "(x, ys) \<in> set (prods g)" "nullable_gamma g ys" by
      cases auto
  have ys_eq: "ys = gpre @ s # gsuf"
  proof -
    have "lookahead_for la x (gpre @ s # gsuf) g"
      by (simp add: FirstGamma FirstNT.hyps(2,3) lookahead_for_def)
    moreover have "lookahead_for la x ys g"
      by (simp add: FirstNT.prems(2) ys_props(2) lookahead_for_def)
    ultimately show ?thesis using assms by
        (metis FirstNT.hyps(1) Pair_inject ys_props(1) option.inject pt_complete_def)
  qed
  have "nullable_sym g s" using ys_props(2) ys_eq nullable_sym_in by fastforce
  then show ?case
  proof (cases s)
    case (NT x)
    have "nullable_gamma g gsuf" using nullable_split[where xs = "gpre @ [s]"] ys_props(2) ys_eq by
        auto
    then have "follow_sym g la s" using FirstNT.hyps(1) FirstNT.prems(2) FollowLeft NT by fastforce
    then show ?thesis using FirstNT.IH \<open>nullable_sym g s\<close> by auto
  next
    case (T t)
    show ?thesis using \<open>nullable_sym g s\<close> T by (cases rule: nullable_sym.cases) auto
  qed
qed

lemma first_sym_rhs_eqs: "parse_table_correct t g \<Longrightarrow> (x, pre @ s # suf) \<in> set (prods g)
  \<Longrightarrow> (x, pre' @ s' # suf') \<in> set (prods g) \<Longrightarrow> nullable_gamma g pre \<Longrightarrow> nullable_gamma g pre'
  \<Longrightarrow> first_sym g la s \<Longrightarrow> first_sym g la s' \<Longrightarrow> pre = pre' \<and> s = s' \<and> suf = suf'"
proof (goal_cases)
  case 1
  have "pre @ s # suf = pre' @ s' # suf'"
  proof -
    have "lookahead_for la x (pre @ s # suf) g" by (simp add: "1"(4,6) FirstGamma lookahead_for_def)
    moreover have "lookahead_for la x (pre' @ s' # suf') g" by
        (simp add: "1"(5,7) FirstGamma lookahead_for_def)
    ultimately show ?thesis
      using "1"(1-3) unfolding pt_complete_def by (metis Pair_inject option.inject)
  qed
  then consider (s_in_pre') "s \<in> set pre'" | (s'_in_pre) "s' \<in> set pre"
    | (eq) "pre = pre' \<and> s = s' \<and> suf = suf'" using medial by fastforce
  then show ?case
  proof cases
    case s_in_pre'
    then have "nullable_sym g s" using "1"(5) using nullable_sym_in by auto
    moreover have "follow_sym g la s"
    proof -
      have "first_gamma g la (s' # suf')" using "1"(7) FirstGamma[of _ "[]" _ s'] NullableNil by
          auto
      then show ?thesis using "1"(3,5) s_in_pre' follow_pre[where suf = "s' # suf'"] by auto
    qed
    ultimately show ?thesis using "1"(1,6) no_first_follow_conflicts by auto
  next
    case s'_in_pre
    then have "nullable_sym g s'" using "1"(4) using nullable_sym_in by auto
    moreover have "follow_sym g la s'"
    proof -
      have "first_gamma g la (s # suf)" using "1"(6) FirstGamma[of _ "[]" _ s] NullableNil by auto
      then show ?thesis using "1"(2,4) s'_in_pre follow_pre[where suf = "s # suf"] by auto
    qed
    ultimately show ?thesis using "1"(1,7) no_first_follow_conflicts by auto
  next
    case eq
    then show ?thesis by blast
  qed
qed

lemma sized_first_sym_det:
  assumes "parse_table_correct t g"
  shows "sized_first_sym g la s n \<Longrightarrow> (\<forall>n'. s = s' \<longrightarrow> sized_first_sym g la s' n' \<longrightarrow> n = n')"
proof (induction arbitrary: s' rule: sized_first_sym.inducts)
  case (SzFirstT g y)
  then show ?case by (auto, cases rule: sized_first_sym.cases) auto
next
  case (SzFirstNT x pre s suf la n)
  have "s' = NT x \<longrightarrow> sized_first_sym g la s' n' \<longrightarrow> Suc n = n'" for n'
  proof (intro impI, goal_cases)
    case 1
    obtain gpre gsuf s0 n0 where s0_props: "(x, gpre @ s0 # gsuf) \<in> set (prods g)"
      "nullable_gamma g gpre" "sized_first_sym g la s0 n0" "n' = Suc n0"
      using 1(1) by (cases rule: sized_first_sym.cases[OF 1(2)]) auto
    then have "first_sym g la s" "first_sym g la s0" using SzFirstNT.hyps(3) sized_fs_fs by auto
    then have "s = s0" using first_sym_rhs_eqs SzFirstNT.hyps s0_props assms by fastforce
    then have "n = n0" using SzFirstNT.IH \<open>sized_first_sym g la s0 n0\<close> by auto
    then show ?case using \<open>n' = Suc n0\<close> by auto
  qed
  then show ?case by auto
qed

lemma sized_first_sym_np: "nullable_path g la x y \<Longrightarrow> first_sym g la y
    \<Longrightarrow>  \<exists>nx ny. sized_first_sym g la x nx \<and> sized_first_sym g la y ny \<and> ny < nx"
proof (induction rule: nullable_path.induct)
  case (DirectPath x gamma g gpre z gsuf la)
  then obtain n where "sized_first_sym g la (NT z) n" using first_sym_exists_size by blast
  then have "sized_first_sym g la (NT x) (Suc n)" using DirectPath.hyps by (simp add: SzFirstNT)
  then show ?case using \<open>sized_first_sym g la (NT z) n\<close> by blast
next
  case (IndirectPath x gamma g gpre y gsuf la z)
  then obtain nx ny where nx_ny_ex:
    "sized_first_sym g la (NT y) nx \<and> sized_first_sym g la (NT z) ny \<and> ny < nx" by auto
  then have "sized_first_sym g la (NT x) (Suc nx)" using IndirectPath.hyps by (simp add: SzFirstNT)
  then show ?case using nx_ny_ex less_SucI by blast
qed

inductive sized_nullable_sym :: "('n, 't) grammar \<Rightarrow> ('n, 't) symbol \<Rightarrow> nat \<Rightarrow> bool"
  and sized_nullable_gamma ::  "('n, 't) grammar \<Rightarrow> ('n, 't) symbol list \<Rightarrow> nat \<Rightarrow> bool" for g where
  SzNullableSym: "(x, gamma) \<in> set (prods g)
    \<Longrightarrow> sized_nullable_gamma g gamma n \<Longrightarrow> sized_nullable_sym g (NT x) (Suc n)"
| SzNullableNil: "sized_nullable_gamma g [] 0"
| SzNullableCons: "sized_nullable_sym g s n \<Longrightarrow> sized_nullable_gamma g ss n'
    \<Longrightarrow> sized_nullable_gamma g (s # ss) (n + n')"

lemma sized_ng_ng: "sized_nullable_sym g s n \<Longrightarrow> nullable_sym g s"
  "sized_nullable_gamma g gamma n \<Longrightarrow> nullable_gamma g gamma"
  by (induction rule: sized_nullable_sym_sized_nullable_gamma.inducts)
    (auto simp add: NullableSym NullableNil NullableCons)

lemma ng_sized_ng: "nullable_sym g s \<Longrightarrow> \<exists>n. sized_nullable_sym g s n"
  "nullable_gamma g gamma \<Longrightarrow> \<exists>n. sized_nullable_gamma g gamma n"
  using SzNullableSym SzNullableNil SzNullableCons
  by (induction rule: nullable_sym_nullable_gamma.inducts) fastforce+

lemma sized_nullable_sym_det':
  assumes"parse_table_correct pt g"
  shows "sized_nullable_sym g s n
    \<Longrightarrow> (\<And>n'. follow_sym g la s \<Longrightarrow> sized_nullable_sym g s n' \<Longrightarrow> n = n')"
    and "sized_nullable_gamma g gsuf n \<Longrightarrow> (\<And>x gpre n'. (x, gpre @ gsuf) \<in> set (prods g)
    \<Longrightarrow> follow_sym g la (NT x) \<Longrightarrow> sized_nullable_gamma g gsuf n' \<Longrightarrow> n = n')"
proof (induction rule: sized_nullable_sym_sized_nullable_gamma.inducts)
  case (SzNullableSym x gamma n)
  from SzNullableSym.prems(2) obtain n0 gamma0 where "(x, gamma0) \<in> set (prods g)"
    "sized_nullable_gamma g gamma0 n0" "n' = Suc n0" by (cases) auto
  have "gamma0 = gamma"
  proof -
    have "lookahead_for la x gamma0 g" unfolding lookahead_for_def
      using sized_ng_ng SzNullableSym.prems(1) \<open>sized_nullable_gamma g gamma0 n0\<close> by blast
    then have lookup_1: "fmlookup pt (x, la) = Some (x, gamma0)"
      using assms \<open>(x, gamma0) \<in> set (prods g)\<close> by (auto simp add: pt_complete_def)
    have "lookahead_for la x gamma g" unfolding lookahead_for_def
      using sized_ng_ng SzNullableSym.prems(1) SzNullableSym.IH(2) by blast
    then have lookup_2: "fmlookup pt (x, la) = Some (x, gamma)" using assms SzNullableSym.IH(1)
      by (auto simp add: pt_complete_def)
    show ?thesis using lookup_1 lookup_2 by auto
  qed
  then have "n0 = n"
    using \<open>sized_nullable_gamma g gamma0 n0\<close> SzNullableSym.IH(3)[of _ "[]"] SzNullableSym.IH(1)
      SzNullableSym.prems(1) by auto
  then show ?case by (simp add: \<open>n' = Suc n0\<close>)
next
  case SzNullableNil
  then show ?case by (cases rule: parse.sized_nullable_gamma.cases) auto
next
  case (SzNullableCons s n1 ss n2 x)
  from SzNullableCons.prems(3) obtain n1' n2' where
    "sized_nullable_sym g s n1'" "sized_nullable_gamma g ss n2'" "n' = n1' + n2'" by (cases) auto
  have "follow_sym g la s"
  proof (cases s)
    case (NT x1)
    have "nullable_gamma g ss" using sized_ng_ng SzNullableCons.IH(3) by fastforce
    then show ?thesis using FollowLeft NT SzNullableCons.prems(1,2) by fastforce
  next
    case (T x2)
    from \<open>sized_nullable_sym g s n1\<close> show ?thesis using T by (cases) auto
  qed
  then have "n1 = n1'" using SzNullableCons.IH(2)[of n1'] \<open>sized_nullable_sym g s n1'\<close> by auto
  moreover have "n2 = n2'"
    using SzNullableCons.IH(4)[of x "gpre @ [s]" n2'] \<open>sized_nullable_gamma g ss n2'\<close>
    by (simp add: SzNullableCons.prems(1,2))
  ultimately show ?case using \<open>n' = n1' + n2'\<close> by auto
qed

lemma sized_nullable_sym_det:
  assumes"parse_table_correct t g"
  shows "sized_nullable_sym g s n \<Longrightarrow> follow_sym g la s \<Longrightarrow> sized_nullable_sym g s n' \<Longrightarrow> n = n'"
  using sized_nullable_sym_det' assms by blast

lemma sym_in_gamma_size_le: "nullable_gamma g gamma \<Longrightarrow> s \<in> set gamma
  \<Longrightarrow> \<exists>n n'. sized_nullable_sym g s n \<and> sized_nullable_gamma g gamma n' \<and> n \<le> n'"
proof (induction gamma)
  case Nil
  then show ?case by auto
next
  case (Cons a gamma)
  from Cons.prems(1) have nullable: "nullable_sym g a" "nullable_gamma g gamma" by
    (cases rule: nullable_gamma.cases, auto)+
  then show ?case
  proof (cases "a = s")
    case True
    then show ?thesis using SzNullableCons nullable ng_sized_ng by fastforce
  next
    case False
    then show ?thesis using Cons.IH Cons.prems(2) SzNullableCons nullable ng_sized_ng(1) by
      fastforce
  qed
qed

lemma sized_ns_np:
  assumes "(x, pre @ NT y # suf) \<in> set (prods g)" "nullable_gamma g (pre @ NT y # suf)"
    "nullable_sym g (NT y)"
  shows "\<exists>nx ny. sized_nullable_sym g (NT x) nx \<and> sized_nullable_sym g (NT y) ny \<and> ny < nx"
proof -
  obtain n n' where
    "sized_nullable_sym g (NT y) n" "sized_nullable_gamma g (pre @ NT y # suf) n'" "n \<le> n'"
    using sym_in_gamma_size_le[of g "pre @ NT y # suf" "NT y"] assms(2) by auto
  then have "sized_nullable_sym g (NT x) (Suc n')"
    using SzNullableSym[where gamma = "pre @ NT y # suf"] assms(1) by auto
  then show ?thesis using \<open>n \<le> n'\<close> \<open>sized_nullable_sym g (NT y) n\<close> le_imp_less_Suc by blast
qed

lemma exist_decreasing_nullable_sym_sizes_in_null_path:
  shows "nullable_path g la x y \<Longrightarrow> parse_table_correct t g \<Longrightarrow> nullable_sym g x
    \<Longrightarrow> follow_sym g la x
    \<Longrightarrow> \<exists>nx ny. sized_nullable_sym g x nx \<and> sized_nullable_sym g y ny \<and> ny < nx"
proof (induction rule: nullable_path.induct)
  case (DirectPath x gamma g pre y suf la)
  from DirectPath.prems(2) obtain ys where "(x, ys) \<in> set (prods g)" "nullable_gamma g ys" by
      (cases rule: nullable_sym.cases) auto
  from DirectPath.hyps(4) consider (fst_gamma) "first_gamma g la gamma"
    | (null_gamma) "nullable_gamma g gamma" "follow_sym g la (NT x)"
    unfolding lookahead_for_def by auto
  then show ?case
  proof cases
    case fst_gamma
    then have "first_sym g la (NT x)" using DirectPath.hyps(1) FirstNT by cases auto
    then have "\<not> follow_sym g la (NT x)" using DirectPath.prems(1,2) by
      (auto simp add: no_first_follow_conflicts)
    then show ?thesis using DirectPath.prems(3) by auto
  next
    case null_gamma
    have "nullable_sym g (NT y)" using DirectPath.hyps(2) null_gamma(1) nullable_sym_in by fastforce
    then show ?thesis using DirectPath.hyps(1,2) null_gamma(1) parse.sized_ns_np by fastforce
  qed
next
  case (IndirectPath x gamma g gpre y gsuf la z)
  from IndirectPath.hyps(4) consider (fst_gamma) "first_gamma g la gamma"
    | (null_gamma) "nullable_gamma g gamma" "follow_sym g la (NT x)"
    unfolding lookahead_for_def by auto
  then show ?case
  proof cases
    case fst_gamma
    then have "first_sym g la (NT x)" using IndirectPath.hyps(1) FirstNT by cases auto
    then have "\<not> follow_sym g la (NT x)" using IndirectPath.prems(1,2) by
        (auto simp add: no_first_follow_conflicts)
    then show ?thesis using IndirectPath.prems(3) by auto
  next
    case null_gamma
    have "nullable_sym g (NT y)" using IndirectPath.hyps(2) null_gamma(1) nullable_sym_in by
        fastforce
    have "nullable_gamma g gsuf"
      using null_gamma(1) IndirectPath.hyps(2) nullable_split[where xs = "gpre @ [NT y]"] by auto
    then have "follow_sym g la (NT y)" using null_gamma IndirectPath.hyps(1,2) by
        (auto simp add: FollowLeft)
    then obtain ny nz where
      "sized_nullable_sym g (NT y) ny" "sized_nullable_sym g (NT z) nz" "nz < ny"
      using IndirectPath.IH IndirectPath.prems(1) \<open>nullable_sym g (NT y)\<close> by auto
    obtain nx ny' where
      "sized_nullable_sym g (NT x) nx" "sized_nullable_sym g (NT y) ny'" "ny' < nx"
      using IndirectPath.hyps(1,2) null_gamma(1) sized_ns_np \<open>nullable_sym g (NT y)\<close> by fastforce
    then have "ny = ny'" using IndirectPath.prems(1) \<open>follow_sym g la (NT y)\<close>
        \<open>sized_nullable_sym g (NT y) ny\<close> sized_nullable_sym_det by blast
    then have "nz < nx" using \<open>ny' < nx\<close> \<open>nz < ny\<close> by auto
    then show ?thesis  using \<open>sized_nullable_sym g (NT x) nx\<close> \<open>sized_nullable_sym g (NT z) nz\<close> by
        auto
  qed
qed

lemma nullable_path_exists_production: "nullable_path g la (NT x) y
  \<Longrightarrow> \<exists>gamma. (x, gamma) \<in> set (prods g) \<and> lookahead_for la x gamma g"
  by (cases rule: nullable_path.cases) auto

lemma ll1_parse_table_impl_no_left_recursion:
  assumes "parse_table_correct tbl (g :: ('n, 't) grammar)"
  shows "\<not> left_recursive g (NT x) la"
proof
  assume x_left_rec: "left_recursive g (NT x) la"
  then obtain gamma where "(x, gamma) \<in> set (prods g)" "lookahead_for la x gamma g"
    using nullable_path_exists_production by fastforce
  then consider "first_gamma g la gamma" | "nullable_gamma g gamma" "follow_sym g la (NT x)"
    by (auto simp: lookahead_for_def)
  then show "False"
  proof (cases)
    case 1
    then have "first_sym g la (NT x)" using FirstNT \<open>(x, gamma) \<in> set (prods g)\<close> by (cases) auto
    then obtain nx ny where "sized_first_sym g la (NT x) nx" "sized_first_sym g la (NT x) ny"
      "ny < nx" using sized_first_sym_np x_left_rec by blast
    then have "ny = nx" using assms sized_first_sym_det by fastforce
    then show ?thesis using \<open>ny < nx\<close> by auto
  next
    case 2
    then have "nullable_sym g (NT x)" using \<open>(x, gamma) \<in> set (prods g)\<close> by
        (auto simp add: NullableSym)
    then obtain n n' where "sized_nullable_sym g (NT x) n" "sized_nullable_sym g (NT x) n'" "n' < n"
      using "2"(2) x_left_rec assms exist_decreasing_nullable_sym_sizes_in_null_path by blast
    then show ?thesis using "2"(2) assms sized_nullable_sym_det by blast
  qed
qed

lemma input_length_lt_or_nullable_sym: "case x of Inl (pt, s, ts, vis) \<Rightarrow> parse_table_correct pt g
    \<longrightarrow> parseSymbol pt s ts vis = RESULT v r \<longrightarrow> length r < length ts \<or> nullable_sym g s
  | Inr (pt, x, ss, ts, vis) \<Rightarrow> parse_table_correct pt g \<longrightarrow> parseGamma pt x ss ts vis = RESULT v r
    \<longrightarrow> length r < length ts \<or> nullable_gamma g ss"
proof (induction arbitrary: v r rule: parse_meas_induct)
  case (1 y)
  note IH = 1
  then show ?case
  proof (cases y)
    case (Inl a)
    then obtain pt s ts vis where "a = (pt, s, ts, vis)" by (cases y) auto
    have "length r < length ts \<or> nullable_sym g s"
      if "parseSymbol pt s ts vis = RESULT v r" and "parse_table_correct pt g"
    proof (cases s)
      case (NT x)
      from that obtain ss where parse_ss_simp: "x |\<notin>| vis" "fmlookup pt (x, peek ts) = Some (x, ss)"
        "parseGamma pt x ss ts (finsert x vis) = RESULT v r"
        by (auto simp: NT split: if_splits option.splits)
      then have "(x, ss) \<in> set (prods g)" using that(2) by (auto simp add: pt_sound_def)
      have "fcard (nt_from_pt pt |-| finsert x vis) < fcard (nt_from_pt pt |-| vis)"
        using fcard_diff_insert_less parse_ss_simp(1,2) by fastforce
      then have "length r < length ts \<or> nullable_gamma g ss"
        using IH[of "Inr (pt, x, ss, ts, finsert x vis)"] parse_ss_simp(3)
        unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
        by (auto simp: Inl \<open>a = (pt, s, ts, vis)\<close> that(2))
      then show ?thesis using NT NullableSym \<open>(x, ss) \<in> set (prods g)\<close> by force
    next
      case (T t)
      from that obtain s where "ts = (t, s) # r"
        by (cases ts, auto simp: T split: if_splits option.splits)
      then show ?thesis by simp
    qed
    then show ?thesis by (simp add: Inl \<open>a = (pt, s, ts, vis)\<close>)
  next
    case (Inr a)
    then obtain pt x ss ts vis where "a = (pt, x, ss, ts, vis)" by (cases y) auto
    have "length r < length ts \<or> nullable_gamma g ss" if
      "parseGamma pt x ss ts vis = RESULT v r" "parse_table_correct pt g"
    proof (cases ss)
      case Nil
      then show ?thesis by (simp add: NullableNil)
    next
      case (Cons s ss')
      from that(1) consider v0 v1 where "parseSymbol pt s ts vis = RESULT v0 ts"
        "parseGamma pt x ss' ts vis = RESULT (Node x v1) r" "v = Node x (v0 # v1)"
      | v0 v1 r0 where "parseSymbol pt s ts vis = RESULT v0 r0" "length r0 < length ts"
        "parseGamma pt x ss' r0 {||} = RESULT (Node x v1) r" "v = Node x (v0 # v1)"
        using parseSymbol_ts_contains_remainder[of pt s ts vis] Cons parseGamma_node(2)[of pt x ss']
        by (fastforce split: return_type.splits parse_tree.splits if_splits)
      then show ?thesis
      proof cases
        case 1
        then have "length ts < length ts \<or> nullable_sym g s"
          using IH[of "Inl (pt, s, ts, vis)"] that(2)
          unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          by (auto simp add: Inr \<open>a = (pt, x, ss, ts, vis)\<close>)
        moreover have "length r < length ts \<or> nullable_gamma g ss'"
          using IH[of "Inr (pt, x, ss', ts, vis)"] that(2) 1
          unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          by (auto simp add: Inr \<open>a = (pt, x, ss, ts, vis)\<close> Cons)
        ultimately show ?thesis using NullableCons Cons by blast
      next
        case 2
        have "length r \<le> length r0" using parseGamma_ts_contains_remainder "2"(3) by fastforce
        then show ?thesis using "2"(2) by auto
      qed
    qed
    then show ?thesis by (simp add: Inr \<open>a = (pt, x, ss, ts, vis)\<close>)
  qed
qed

lemma input_length_eq_nullable_sym:
  "parse_table_correct tbl g \<Longrightarrow> parseSymbol tbl s ts vis = RESULT v ts \<Longrightarrow> nullable_sym g s"
  using input_length_lt_or_nullable_sym[where x = "Inl (tbl, s, ts, vis)"] by auto

lemma error_conditions: "case y of
    Inl (pt, s, ts, vis) \<Rightarrow> parse_table_correct pt g \<longrightarrow> parseSymbol pt s ts vis = ERROR m z ts'
      \<longrightarrow> ((z |\<in>| vis \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z)))
      \<or> (\<exists>la. left_recursive g (NT z) la))
  | Inr (pt, x, ss, ts, vis) \<Rightarrow> parse_table_correct pt g \<longrightarrow>
      parseGamma pt x ss ts vis = ERROR m z ts' \<longrightarrow> (\<exists>pre s suf. ss = pre @ s # suf
      \<and> nullable_gamma g pre \<and> z |\<in>| vis \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z)))
      \<or> (\<exists>la. (left_recursive g (NT z) la))"
proof (induction arbitrary: m z ts' rule: parse_meas_induct)
  case (1 y)
  note IH = "1"
  then show ?case
  proof (cases y)
    case (Inl a)
    then obtain pt s ts vis where "a = (pt, s, ts, vis)" using prod_cases4 by blast
    then show ?thesis
    proof (cases s)
      case (NT x)
      consider (x_in_vis) "x |\<in>| vis" | (lookup_none) "fmlookup pt (x, peek ts) = None"
        | (lookup_some_neq) x' ss' where "x |\<notin>| vis" "x \<noteq> x'"
          "fmlookup pt (x, peek ts) = Some (x',ss')"
        | (lookup_some_eq )ss' where "x |\<notin>| vis" "fmlookup pt (x, peek ts) = Some (x, ss')"
        by fastforce
      then show ?thesis
      proof (cases)
        case lookup_some_eq
        then have "fcard (nt_from_pt pt |-| finsert x vis) < fcard (nt_from_pt pt |-| vis)"
          using fcard_diff_insert_less[of x] by auto
        then have IH': "parse_table_correct pt g
            \<Longrightarrow> parseGamma pt x ss' ts (finsert x vis) = ERROR m z ts'
            \<Longrightarrow> ((\<exists>pre s suf. ss' = pre @ s # suf \<and> nullable_gamma g pre \<and> z |\<in>| (finsert x vis)
            \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z)))
            \<or> (\<exists>la. left_recursive g (NT z) la))"
          using IH[of "Inr (pt, x, ss', ts, (finsert x vis))" m z ts']
          unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          by (auto simp add: Inl \<open>a = (pt, s, ts, vis)\<close>)
        have "parse_table_correct pt g \<Longrightarrow> parseSymbol pt s ts vis = ERROR m z ts'
          \<Longrightarrow> z |\<in>| vis \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z))
              \<or> (\<exists>la. left_recursive g (NT z) la)"
        proof -
          assume assms: "parse_table_correct pt g" "parseSymbol pt s ts vis = ERROR m z ts'"
          have "parseGamma pt x ss' ts (finsert x vis) = ERROR m z ts'"
            using assms(2) lookup_some_eq NT by auto
          then consider pre s' suf where "ss' = pre @ s' # suf" "nullable_gamma g pre"
            "z |\<in>| (finsert x vis)" "s' = NT z \<or> nullable_path g (peek ts) s' (NT z)"
          | la where "left_recursive g (NT z) la" using IH' assms(1,2) by auto
          then show "z |\<in>| vis \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z))
            \<or> (\<exists>la. left_recursive g (NT z) la)"
          proof (cases)
            case 1
            have "fmlookup pt (x,(peek ts)) = Some (x, pre @ s' # suf)"
              using "1"(1) lookup_some_eq(2) by blast
            then have x_la: "(x, pre @ s' # suf) \<in> set (prods g)"
              "lookahead_for (peek ts) x (pre @ s' # suf) g" using \<open>parse_table_correct pt g\<close>
              by (simp_all add: pt_sound_def)
            consider (s'_is_ntz) "s' = NT z" | (null_path) "nullable_path g (peek ts) s' (NT z)"
              using "1"(4) by auto
            then show ?thesis
            proof (cases)
              case s'_is_ntz
              then show ?thesis using "1"(2-4) DirectPath NT  x_la by fastforce
            next
              case null_path
              then obtain n n' where "s' = NT n" "NT x = NT n'" by cases auto
              then show ?thesis using "1"(2,3) IndirectPath null_path x_la NT by fastforce
            qed
          next
            case 2
            then show ?thesis by blast
          qed
        qed
        then show ?thesis by (simp add: Inl \<open>a = (pt, s, ts, vis)\<close>)
      qed (auto simp add: Inl NT \<open>a = (pt, s, ts, vis)\<close> pt_sound_def)
    next
      case (T _)
      then show ?thesis using Inl T \<open>a = (pt, s, ts, vis)\<close> by (cases ts) auto
    qed
  next
    case (Inr a)
    then obtain pt x ss ts vis where "a = (pt, x, ss, ts, vis)" using prod_cases5 by blast
    have "parse_table_correct pt g \<Longrightarrow> parseGamma pt x ss ts vis = ERROR m z ts'
      \<Longrightarrow> (\<exists>pre s. (\<exists>suf. ss = pre @ s # suf) \<and> nullable_gamma g pre \<and> z |\<in>| vis
          \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z))) \<or> (\<exists>la. left_recursive g (NT z) la)"
    proof -
      assume assms: "parse_table_correct pt g" "parseGamma pt x ss ts vis = ERROR m z ts'"
      then obtain s ss' where "ss = s # ss'" by (auto elim: parseGamma.elims)
      then consider (parse_s_error) "parseSymbol pt s ts vis = ERROR m z ts'"
        | (parse_ss'_error_le) str r where "parseSymbol pt s ts vis = RESULT str r"
          "length r < length ts" "parseGamma pt x ss' r {||} = ERROR m z ts'"
        | (parse_ss'_error_eq) str where "parseSymbol pt s ts vis = RESULT str ts"
          "parseGamma pt x ss' ts vis = ERROR m z ts'"
        using assms(2) parseSymbol_ts_contains_remainder
        by (fastforce split: return_type.splits if_splits parse_tree.splits)
      then show "(\<exists>pre s. (\<exists>suf. ss = pre @ s # suf) \<and> nullable_gamma g pre \<and> z |\<in>| vis
        \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z))) \<or>
        (\<exists>la. left_recursive g (NT z) la)"
      proof cases
        case parse_s_error
        have "parse_table_correct pt g \<longrightarrow> parseSymbol pt s ts vis = ERROR m z ts'
            \<longrightarrow> z |\<in>| vis \<and> (s = NT z \<or> nullable_path g (peek ts) s (NT z))
            \<or> (\<exists>la. left_recursive g (NT z) la)"
          using IH[of "Inl (pt, s, ts, vis)" m z ts'] assms
          unfolding mlex_triple_def parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          by (auto simp add: Inr \<open>a = (pt, x, ss, ts, vis)\<close>)
        then show ?thesis using NullableNil \<open>ss = s # ss'\<close> assms(1) parse_s_error by blast
      next
        case parse_ss'_error_le
        then have "(parse_ind_meas_sym_list pt ss' r {||},
          parse_ind_meas_sym_list pt ss ts vis) \<in> lex_triple less_than less_than less_than"
          unfolding parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          using \<open>ss = s # ss'\<close> parse_ss'_error_le(2) by auto
        then show ?thesis using IH[of "Inr (pt, x, ss', r, {||})" m z] assms parse_ss'_error_le(3)
          by (auto simp add: mlex_triple_def Inr \<open>a = (pt, x, ss, ts, vis)\<close>)
      next
        case parse_ss'_error_eq
        have "(parse_ind_meas_sym_list pt ss' ts vis,
          parse_ind_meas_sym_list pt ss ts vis) \<in> lex_triple less_than less_than less_than"
          unfolding parse_ind_meas_sym_def parse_ind_meas_sym_list_def
          using \<open>ss = s # ss'\<close> by auto
        then consider pre s0 suf where "ss' = pre @ s0 # suf" "nullable_gamma g pre" "z |\<in>| vis"
          "(s0 = NT z \<or> nullable_path g (peek ts) s0 (NT z))"
        | la where "left_recursive g (NT z) la"
          using IH[of "Inr (pt, x, ss', ts, vis)" m z ts'] assms parseSymbol_ts_contains_remainder
          by (auto simp add: mlex_triple_def Inr \<open>a = (pt, x, ss, ts, vis)\<close> parse_ss'_error_eq(2))
        then show ?thesis
        proof cases
          case 1
          have "nullable_sym g s"
            using input_length_eq_nullable_sym assms(1) parse_ss'_error_eq(1) by fastforce
          then have "nullable_gamma g (s # pre)" by (simp add: "1"(2) NullableCons)
          then show ?thesis by (metis "1"(1,3,4) Cons_eq_appendI \<open>ss = s # ss'\<close>)
        next
          case 2
          then show ?thesis by auto
        qed
      qed
    qed
    then show ?thesis by (simp add: Inr \<open>a = (pt, x, ss, ts, vis)\<close>)
  qed
qed

theorem parse_terminates_without_error:
  "parse_table_correct pt g \<Longrightarrow> parse (PT pt) s (w @ r) \<noteq> ERROR m x ts'"
proof
  assume A: "parse_table_correct pt g" "parse (PT pt) s (w @ r) = ERROR m x ts'"
  then have "\<not> (\<exists>la. left_recursive g (NT x) la)" using ll1_parse_table_impl_no_left_recursion
    using \<open>parse_table_correct pt g\<close> by fastforce
  then have "(x |\<in>| {||} \<and> (s = NT x \<or> nullable_path g (peek (w @ r)) s (NT x)))"
    using error_conditions[of g m x ts' "Inl (pt, s, (w @ r), {||})"] A by auto
  then show "False" by auto
qed

theorem parse_complete: "parse_table_correct pt g \<Longrightarrow> sym_derives_prefix g s w v r
  \<Longrightarrow> parse (PT pt) s (w @ r) = RESULT v r"
  using parse_terminates_without_error parse_complete_or_error by fastforce

end

declare parse.parseSymbol.simps [code]
declare parse.parseGamma.simps [code]
declare parse.parse.simps [code]
declare parse.parseToString.simps [code]
declare parse.parseTreeToString.simps [code]
declare parse.mismatchMessage_def [code]

end