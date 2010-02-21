(*
 * Lazy lists.
 * (C)opyright 2009, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

(*<*)
theory LList
imports HOLCF Nats
begin
(*>*)

section{* The fully-lazy list type. *}

domain 'a llist =
    lnil ("lnil")
  | lcons (lazy "'a") (lazy "'a llist") (infixr ":@" 65)

lemma llist_case_distr_strict:
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> f\<cdot>(llist_when\<cdot>g\<cdot>h\<cdot>xxs) = llist_when\<cdot>(f\<cdot>g)\<cdot>(\<Lambda> x xs. f\<cdot>(h\<cdot>x\<cdot>xs))\<cdot>xxs"
  by (cases xxs) simp_all

fixrec lsingleton :: "'a \<rightarrow> 'a llist"
where
  "lsingleton\<cdot>x = x :@ lnil"

fixrec lappend :: "'a llist \<rightarrow> 'a llist \<rightarrow> 'a llist"
where
  "lappend\<cdot>lnil\<cdot>ys = ys"
| "lappend\<cdot>(x :@ xs)\<cdot>ys = x :@ (lappend\<cdot>xs\<cdot>ys)"

abbreviation
  lappend_syn :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" (infixr ":++" 65) where
  "xs :++ ys \<equiv> lappend\<cdot>xs\<cdot>ys"

fixpat lappend_strict': "lappend\<cdot>\<bottom>"

text{* This gives us that @{thm lappend_strict'}. *}

text {* This is where we use @{thm inst_cfun_pcpo} *}
lemma lappend_strict[simp]: "lappend\<cdot>\<bottom> = \<bottom>"
  by (rule ext_cfun) (simp add: lappend_strict')

lemma lappend_assoc: "(xs :++ ys) :++ zs = xs :++ (ys :++ zs)"
  by (induct xs rule: llist.ind, simp_all)

lemma lappend_lnil_id_left[simp]: "lappend\<cdot>lnil = ID"
  by (rule ext_cfun) simp

lemma lappend_lnil_id_right[simp]: "xs :++ lnil = xs"
  by (induct xs rule: llist.ind) simp_all

fixrec lconcat :: "'a llist llist \<rightarrow> 'a llist"
where
  "lconcat\<cdot>lnil = lnil"
| "lconcat\<cdot>(x :@ xs) = x :++ lconcat\<cdot>xs"

fixpat lconcat_strict[simp]:
  "lconcat\<cdot>\<bottom>"

fixrec lall :: "('a \<rightarrow> tr) \<rightarrow> 'a llist \<rightarrow> tr"
where
  "lall\<cdot>p\<cdot>lnil = TT"
| "lall\<cdot>p\<cdot>(x :@ xs) = (p\<cdot>x andalso lall\<cdot>p\<cdot>xs)"

fixpat lall_strict[simp]: "lall\<cdot>p\<cdot>\<bottom>"

fixrec lfilter :: "('a \<rightarrow> tr) \<rightarrow> 'a llist \<rightarrow> 'a llist"
where
  "lfilter\<cdot>p\<cdot>lnil = lnil"
| "lfilter\<cdot>p\<cdot>(x :@ xs) = If p\<cdot>x then x :@ lfilter\<cdot>p\<cdot>xs else lfilter\<cdot>p\<cdot>xs fi"

fixpat lfilter_strict[simp]: "lfilter\<cdot>p\<cdot>\<bottom>"

lemma lfilter_const_true: "lfilter\<cdot>(\<Lambda> x. TT)\<cdot>xs = xs"
  by (induct xs rule: llist.ind, simp_all)

lemma lfilter_lnil: "(lfilter\<cdot>p\<cdot>xs = lnil) = (lall\<cdot>(neg oo p)\<cdot>xs = TT)"
proof(induct xs rule: llist.ind)
  fix a l assume indhyp: "(lfilter\<cdot>p\<cdot>l = lnil) = (lall\<cdot>(Tr.neg oo p)\<cdot>l = TT)"
  thus "(lfilter\<cdot>p\<cdot>(a :@ l) = lnil) = (lall\<cdot>(Tr.neg oo p)\<cdot>(a :@ l) = TT)"
    by (cases "p\<cdot>a" rule: trE, simp_all)
qed simp_all

lemma filter_filter: "lfilter\<cdot>p\<cdot>(lfilter\<cdot>q\<cdot>xs) = lfilter\<cdot>(\<Lambda> x. q\<cdot>x andalso p\<cdot>x)\<cdot>xs"
proof(induct xs rule: llist.ind)
  fix a l assume "lfilter\<cdot>p\<cdot>(lfilter\<cdot>q\<cdot>l) = lfilter\<cdot>(\<Lambda>(x\<Colon>'a). q\<cdot>x andalso p\<cdot>x)\<cdot>l"
  thus "lfilter\<cdot>p\<cdot>(lfilter\<cdot>q\<cdot>(a :@ l)) = lfilter\<cdot>(\<Lambda>(x\<Colon>'a). q\<cdot>x andalso p\<cdot>x)\<cdot>(a :@ l)"
    by (cases "q\<cdot>a" rule: trE, simp_all)
qed simp_all

fixrec ldropWhile :: "('a \<rightarrow> tr) \<rightarrow> 'a llist \<rightarrow> 'a llist"
where
  "ldropWhile\<cdot>p\<cdot>lnil = lnil"
| "ldropWhile\<cdot>p\<cdot>(x :@ xs) = If p\<cdot>x then ldropWhile\<cdot>p\<cdot>xs else x :@ xs fi"

fixpat ldropWhile_strict[simp]: "ldropWhile\<cdot>p\<cdot>\<bottom>"

lemma ldropWhile_lnil: "(ldropWhile\<cdot>p\<cdot>xs = lnil) = (lall\<cdot>p\<cdot>xs = TT)"
proof(induct xs rule: llist.ind)
  fix a l assume "(ldropWhile\<cdot>p\<cdot>l = lnil) = (lall\<cdot>p\<cdot>l = TT)"
  thus "(ldropWhile\<cdot>p\<cdot>(a :@ l) = lnil) = (lall\<cdot>p\<cdot>(a :@ l) = TT)"
    by (cases "p\<cdot>a" rule: trE, simp_all)
qed simp_all

fixrec literate :: "('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a llist"
where
  "literate\<cdot>f\<cdot>x = x :@ literate\<cdot>f\<cdot>(f\<cdot>x)"

declare literate_simps[simp del]

text{* This order of tests is convenient for the nub proof. I can
imagine the other would be convenient for other proofs... *}

fixrec lmember :: "('a \<rightarrow> 'a \<rightarrow> tr) \<rightarrow> 'a \<rightarrow> 'a llist \<rightarrow> tr"
where
  "lmember\<cdot>eq\<cdot>x\<cdot>lnil = FF"
| "lmember\<cdot>eq\<cdot>x\<cdot>(lcons\<cdot>y\<cdot>ys) = (lmember\<cdot>eq\<cdot>x\<cdot>ys orelse eq\<cdot>y\<cdot>x)"

fixpat lmember_strict[simp]: "lmember\<cdot>eq\<cdot>x\<cdot>\<bottom>"

fixrec llength :: "'a llist \<rightarrow> Nat"
where
  "llength\<cdot>lnil = 0"
| "llength\<cdot>(lcons\<cdot>x\<cdot>xs) = 1 + llength\<cdot>xs"

fixpat llength_strict[simp]: "llength\<cdot>\<bottom>"

fixrec lmap :: "('a \<rightarrow> 'b) \<rightarrow> 'a llist \<rightarrow> 'b llist"
where
  "lmap\<cdot>f\<cdot>lnil = lnil"
| "lmap\<cdot>f\<cdot>(x :@ xs) = f\<cdot>x :@ lmap\<cdot>f\<cdot>xs"

fixpat lmap_strict[simp]: "lmap\<cdot>f\<cdot>\<bottom>"

lemma lconcat_lmap_lsingleton: "lconcat\<cdot>(lmap\<cdot>(\<Lambda> x. x :@ lnil)\<cdot>xs) = xs"
  by (induct xs) simp_all

text{* This @{term "zipWith"} function is only fully defined if the
lists have the same length. *}

fixrec lzipWith0 :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> 'a llist \<rightarrow> 'b llist \<rightarrow> 'c llist"
where
  "lzipWith0\<cdot>f\<cdot>(a :@ as)\<cdot>(b :@ bs) = f\<cdot>a\<cdot>b :@ lzipWith0\<cdot>f\<cdot>as\<cdot>bs"
| "lzipWith0\<cdot>f\<cdot>lnil\<cdot>lnil = lnil"

fixpat lzipWith0_stricts [simp]:
  "lzipWith0\<cdot>f\<cdot>\<bottom>\<cdot>ys"
  "lzipWith0\<cdot>f\<cdot>lnil\<cdot>\<bottom>"
  "lzipWith0\<cdot>f\<cdot>(x :@ xs)\<cdot>\<bottom>"

fixpat lzipWith0_undefs [simp]:
  "lzipWith0\<cdot>f\<cdot>lnil\<cdot>(y :@ ys)"
  "lzipWith0\<cdot>f\<cdot>(x :@ xs)\<cdot>lnil"

text{* This @{term "zipWith"} function follows Haskell's in being more
permissive: zipping uneven lists results in a list as long as the
shortest one. This is what the backtracking monad expects. *}

fixrec (permissive) lzipWith :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> 'a llist \<rightarrow> 'b llist \<rightarrow> 'c llist"
where
  "lzipWith\<cdot>f\<cdot>(a :@ as)\<cdot>(b :@ bs) = f\<cdot>a\<cdot>b :@ lzipWith\<cdot>f\<cdot>as\<cdot>bs"
| "lzipWith\<cdot>f\<cdot>xs\<cdot>ys = lnil"

fixpat lzipWith_simps [simp]:
  "lzipWith\<cdot>f\<cdot>(x :@ xs)\<cdot>(y :@ ys)"
  "lzipWith\<cdot>f\<cdot>(x :@ xs)\<cdot>lnil"
  "lzipWith\<cdot>f\<cdot>lnil\<cdot>(y :@ ys)"
  "lzipWith\<cdot>f\<cdot>lnil\<cdot>lnil"

fixpat lzipWith_stricts [simp]:
  "lzipWith\<cdot>f\<cdot>\<bottom>\<cdot>ys"
  "lzipWith\<cdot>f\<cdot>(x :@ xs)\<cdot>\<bottom>"

(*<*)
end
(*>*)
