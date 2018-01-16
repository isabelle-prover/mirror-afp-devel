(*  Title:      Monomorphic_Monad.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory Monomorphic_Monad imports
  "HOL-Probability.Probability"
  "HOL-Library.Multiset"
begin

lemma (in comp_fun_idem) fold_set_union:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> Finite_Set.fold f x (A \<union> B) = Finite_Set.fold f (Finite_Set.fold f x A) B"
by(induction A arbitrary: x rule: finite_induct)(simp_all add: fold_insert_idem2 del: fold_insert_idem)

lemma (in comp_fun_idem) ffold_set_union: "ffold f x (A |\<union>| B) = ffold f (ffold f x A) B"
including fset.lifting by(transfer fixing: f)(rule fold_set_union)

lemma relcompp_top_top [simp]: "top OO top = top"
by(auto simp add: fun_eq_iff)

attribute_setup locale_witness = \<open>Scan.succeed Locale.witness_add\<close>

named_theorems monad_unfold "Defining equations for overloaded monad operations"

context includes lifting_syntax begin

inductive rel_itself :: "'a itself \<Rightarrow> 'b itself \<Rightarrow> bool"
where "rel_itself TYPE(_) TYPE(_)"

lemma type_parametric [transfer_rule]: "rel_itself TYPE('a) TYPE('b)"
by(simp add: rel_itself.simps)

end

section \<open>Locales for monomorphic monads\<close>

subsection \<open>Plain monad\<close>

type_synonym ('a, 'm) bind = "'m \<Rightarrow> ('a \<Rightarrow> 'm) \<Rightarrow> 'm"
type_synonym ('a, 'm) return = "'a \<Rightarrow> 'm"

locale monad_base =
  fixes return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
begin

primrec sequence :: "'m list \<Rightarrow> ('a list \<Rightarrow> 'm) \<Rightarrow> 'm"
where
  "sequence [] f = f []"
| "sequence (x # xs) f = bind x (\<lambda>a. sequence xs (f \<circ> (#) a))"

definition lift :: "('a \<Rightarrow> 'a) \<Rightarrow> 'm \<Rightarrow> 'm"
where "lift f x = bind x (\<lambda>x. return (f x))"

end

declare
  monad_base.sequence.simps [code]
  monad_base.lift_def [code]

context includes lifting_syntax begin

lemma sequence_parametric [transfer_rule]:
  "((M ===> (A ===> M) ===> M) ===> list_all2 M ===> (list_all2 A ===> M) ===> M) monad_base.sequence monad_base.sequence"
unfolding monad_base.sequence_def[abs_def] by transfer_prover

lemma lift_parametric [transfer_rule]:
  "((A ===> M) ===> (M ===> (A ===> M) ===> M) ===> (A ===> A) ===> M ===> M) monad_base.lift monad_base.lift"
unfolding monad_base.lift_def by transfer_prover

end

locale monad = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  assumes bind_assoc: "\<And>(x :: 'm) f g. bind (bind x f) g = bind x (\<lambda>y. bind (f y) g)" 
  and return_bind: "\<And>x f. bind (return x) f = f x"
  and bind_return: "\<And>x. bind x return = x"
begin

lemma bind_lift [simp]: "bind (lift f x) g = bind x (g \<circ> f)"
by(simp add: lift_def bind_assoc return_bind o_def)

lemma lift_bind [simp]: "lift f (bind m g) = bind m (\<lambda>x. lift f (g x))"
by(simp add: lift_def bind_assoc)

end

subsection \<open>State\<close>

type_synonym ('s, 'm) get = "('s \<Rightarrow> 'm) \<Rightarrow> 'm"
type_synonym ('s, 'm) put = "'s \<Rightarrow> 'm \<Rightarrow> 'm"

locale monad_state_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
begin

definition update :: "('s \<Rightarrow> 's) \<Rightarrow> 'm \<Rightarrow> 'm"
where "update f m = get (\<lambda>s. put (f s) m)"

end

declare monad_state_base.update_def [code]

lemma update_parametric [transfer_rule]: includes lifting_syntax shows  
  "(((S ===> M) ===> M) ===> (S ===> M ===> M) ===> (S ===> S) ===> M ===> M)
   monad_state_base.update monad_state_base.update"
unfolding monad_state_base.update_def by transfer_prover

locale monad_state = monad_state_base return bind get put + monad return bind 
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
  +
  assumes put_get: "\<And>f. put s (get f) = put s (f s)"
  and get_get: "\<And>f. get (\<lambda>s. get (f s)) = get (\<lambda>s. f s s)"
  and put_put: "put s (put s' m) = put s' m"
  and get_put: "get (\<lambda>s. put s m) = m"
  and get_const: "\<And>m. get (\<lambda>_. m) = m"
  and bind_get: "\<And>f g. bind (get f) g = get (\<lambda>s. bind (f s) g)"
  and bind_put: "\<And>f. bind (put s m) f = put s (bind m f)"
begin

lemma put_update: "put s (update f m) = put (f s) m"
by(simp add: update_def put_get put_put)

lemma update_put: "update f (put s m) = put s m"
by(simp add: update_def put_put get_const)

lemma bind_update: "bind (update f m) g = update f (bind m g)"
by(simp add: update_def bind_get bind_put)

lemma update_get: "update f (get g) = get (update f \<circ> g \<circ> f)"
by(simp add: update_def put_get get_get o_def) 
 
lemma update_const: "update (\<lambda>_. s) m = put s m"
by(simp add: update_def get_const)

lemma update_update: "update f (update g m) = update (g \<circ> f) m"
by(simp add: update_def put_get put_put)

lemma update_id: "update id m = m"
by(simp add: update_def get_put)

end

subsection \<open>Failure\<close>

type_synonym 'm fail = "'m"

locale monad_fail_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes fail :: "'m fail"
begin

definition assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'm \<Rightarrow> 'm"
where "assert P m = bind m (\<lambda>x. if P x then return x else fail)"

end

declare monad_fail_base.assert_def [code]

lemma assert_parametric [transfer_rule]: includes lifting_syntax shows
  "((A ===> M) ===> (M ===> (A ===> M) ===> M) ===> M ===> (A ===> (=)) ===> M ===> M)
   monad_fail_base.assert monad_fail_base.assert"
unfolding monad_fail_base.assert_def by transfer_prover

locale monad_fail = monad_fail_base return bind fail + monad return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and fail :: "'m fail"
  +
  assumes fail_bind: "\<And>f. bind fail f = fail"
begin

lemma assert_fail: "assert P fail = fail"
by(simp add: assert_def fail_bind)

end

subsection \<open>Exception\<close>

type_synonym 'm catch = "'m \<Rightarrow> 'm \<Rightarrow> 'm"

locale monad_catch_base = monad_fail_base return bind fail
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and fail :: "'m fail"
  +
  fixes catch :: "'m catch"

locale monad_catch = monad_catch_base return bind fail catch + monad_fail return bind fail
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and fail :: "'m fail"
  and catch :: "'m catch"
  +
  assumes catch_return: "catch (return x) m = return x"
  and catch_fail: "catch fail m = m"
  and catch_fail2: "catch m fail = m"
  and catch_assoc: "catch (catch m m') m'' = catch m (catch m' m'')"

locale monad_catch_state = monad_catch return bind fail catch + monad_state return bind get put
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and fail :: "'m fail"
  and catch :: "'m catch"
  and get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
  +
  assumes catch_get: "catch (get f) m = get (\<lambda>s. catch (f s) m)"
  and catch_put: "catch (put s m) m' = put s (catch m m')"
begin

lemma catch_update: "catch (update f m) m' = update f (catch m m')"
by(simp add: update_def catch_get catch_put)

end

subsection \<open>Reader\<close>

text \<open>As ask takes a continuation, we have to restate the monad laws for ask\<close>

type_synonym ('r, 'm) ask = "('r \<Rightarrow> 'm) \<Rightarrow> 'm"

locale monad_reader_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes ask :: "('r, 'm) ask"

locale monad_reader = monad_reader_base return bind ask + monad return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and ask :: "('r, 'm) ask"
  +
  assumes ask_ask: "\<And>f. ask (\<lambda>r. ask (f r)) = ask (\<lambda>r. f r r)"
  and ask_const: "ask (\<lambda>_. m) = m"
  and bind_ask: "\<And>f g. bind (ask f) g = ask (\<lambda>r. bind (f r) g)"
  and bind_ask2: "\<And>f. bind m (\<lambda>x. ask (f x)) = ask (\<lambda>r. bind m (\<lambda>x. f x r))"
begin

lemma ask_bind: "ask (\<lambda>r. bind (f r) (g r)) = bind (ask f) (\<lambda>x. ask (\<lambda>r. g r x))"
by(simp add: bind_ask bind_ask2 ask_ask)

end

locale monad_reader_state =
  monad_reader return bind ask +
  monad_state return bind get put
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and ask :: "('r, 'm) ask"
  and get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
  +
  assumes ask_get: "\<And>f. ask (\<lambda>r. get (f r)) = get (\<lambda>s. ask (\<lambda>r. f r s))"
  and put_ask: "\<And>f. put s (ask f) = ask (\<lambda>r. put s (f r))"

subsection \<open>Probability\<close>

type_synonym ('p, 'm) sample = "'p pmf \<Rightarrow> ('p \<Rightarrow> 'm) \<Rightarrow> 'm"

locale monad_prob_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes sample :: "('p, 'm) sample"

locale monad_prob = monad return bind + monad_prob_base return bind sample
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and sample :: "('p, 'm) sample"
  +
  assumes sample_const: "\<And>p m. sample p (\<lambda>_. m) = m"
  and sample_return_pmf: "\<And>x f. sample (return_pmf x) f = f x"
  and sample_bind_pmf: "\<And>p f g. sample (bind_pmf p f) g = sample p (\<lambda>x. sample (f x) g)"
  and sample_commute: "\<And>p q f. sample p (\<lambda>x. sample q (f x)) = sample q (\<lambda>y. sample p (\<lambda>x. f x y))"
  \<comment> \<open>We'd like to state that we can combine independent samples rather than just commute them, but that's not possible with a monomorphic sampling operation\<close>
  and bind_sample1: "\<And>p f g. bind (sample p f) g = sample p (\<lambda>x. bind (f x) g)"
  and bind_sample2: "\<And>m f p. bind m (\<lambda>y. sample p (f y)) = sample p (\<lambda>x. bind m (\<lambda>y. f y x))"
  and sample_cong: "\<And>p f g. (\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> sample p f = sample p g"

locale monad_state_prob = monad_state return bind get put + monad_prob return bind sample
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
  and sample :: "('p, 'm) sample"
  +
  assumes sample_get: "sample p (\<lambda>x. get (f x)) = get (\<lambda>s. sample p (\<lambda>x. f x s))"
begin

lemma sample_put: "sample p (\<lambda>x. put s (m x)) = put s (sample p m)"
proof -
  fix UU
  have "sample p (\<lambda>x. put s (m x)) = sample p (\<lambda>x. bind (put s (return UU)) (\<lambda>_. m x))"
    by(simp add: bind_put return_bind)
  also have "\<dots> = bind (put s (return UU)) (\<lambda>_. sample p m)"
    by(simp add: bind_sample2)
  also have "\<dots> = put s (sample p m)"
    by(simp add: bind_put return_bind)
  finally show ?thesis .
qed

lemma sample_update: "sample p (\<lambda>x. update f (m x)) = update f (sample p m)"
by(simp add: update_def sample_get sample_put)

end

subsection \<open>Nondeterministic choice\<close>

type_synonym 'm alt = "'m \<Rightarrow> 'm \<Rightarrow> 'm"

locale monad_alt_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes alt :: "'m alt"

locale monad_alt = monad return bind + monad_alt_base return bind alt
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and alt :: "'m alt"
  + \<comment> \<open>Laws taken from Gibbons, Hinze: Just do it\<close>
  assumes alt_assoc: "alt (alt m1 m2) m3 = alt m1 (alt m2 m3)"
  and bind_alt1: "bind (alt m m') f = alt (bind m f) (bind m' f)"

locale monad_fail_alt = monad_fail return bind fail + monad_alt return bind alt
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and fail :: "'m fail"
  and alt :: "'m alt"
  +
  assumes alt_fail1: "alt fail m = m"
  and alt_fail2: "alt m fail = m"
begin

lemma assert_alt: "assert P (alt m m') = alt (assert P m) (assert P m')"
by(simp add: assert_def bind_alt1)

end

subsection \<open>Writer monad\<close>

type_synonym ('w, 'm) tell = "'w \<Rightarrow> 'm \<Rightarrow> 'm"

locale monad_writer_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes tell :: "('w, 'm) tell"

locale monad_writer = monad_writer_base return bind tell + monad return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and tell :: "('w, 'm) tell"
  +
  assumes bind_tell: "\<And>w m f. bind (tell w m) f = tell w (bind m f)"

subsection \<open>Resumption monad\<close>

type_synonym ('o, 'i, 'm) pause = "'o \<Rightarrow> ('i \<Rightarrow> 'm) \<Rightarrow> 'm"

locale monad_resumption_base = monad_base return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  fixes pause :: "('o, 'i, 'm) pause"

locale monad_resumption = monad_resumption_base return bind pause + monad return bind 
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and pause :: "('o, 'i, 'm) pause"
  +
  assumes bind_pause: "bind (pause out c) f = pause out (\<lambda>i. bind (c i) f)"

subsection \<open>Commutative monad\<close>

locale monad_commute = monad return bind 
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  assumes bind_commute: "bind m (\<lambda>x. bind m' (f x)) = bind m' (\<lambda>y. bind m (\<lambda>x. f x y))"

subsection \<open>Discardable monad\<close>

locale monad_discard = monad return bind
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  +
  assumes bind_const: "bind m (\<lambda>_. m') = m'"


section \<open>Monad implementations\<close>

subsection \<open>Identity monad\<close>

text \<open>We need a type constructor such that we can overload the monad operations\<close>

datatype 'a id = return_id ("extract": 'a)

lemmas return_id_parametric = id.ctr_transfer

subsubsection \<open>Plain monad\<close>

primrec bind_id :: "('a, 'a id) bind"
where "bind_id (return_id x) f = f x"

lemma extract_bind [simp]: "extract (bind_id x f) = extract (f (extract x))"
by(cases x) simp

lemma bind_id_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_id A ===> (A ===> rel_id A) ===> rel_id A) bind_id bind_id"
unfolding bind_id_def by transfer_prover

lemma monad_id [locale_witness]: "monad return_id bind_id"
proof
  show "bind_id (bind_id x f) g = bind_id x (\<lambda>x. bind_id (f x) g)" 
    for x :: "'a id" and f :: "'a \<Rightarrow> 'a id" and g :: "'a \<Rightarrow> 'a id"
    by(rule id.expand) simp
  show "bind_id (return_id x) f = f x" for f :: "'a \<Rightarrow> 'a id" and x
    by(rule id.expand) simp
  show "bind_id x return_id = x" for x :: "'a id"
    by(rule id.expand) simp
qed

lemma monad_commute_id [locale_witness]: "monad_commute return_id bind_id"
proof
  show "bind_id m (\<lambda>x. bind_id m' (f x)) = bind_id m' (\<lambda>y. bind_id m (\<lambda>x. f x y))" for m m' :: "'a id" and f
    by(rule id.expand) simp
qed

lemma monad_discard_id [locale_witness]: "monad_discard return_id bind_id"
proof
  show "bind_id m (\<lambda>_. m') = m'" for m m' :: "'a id" by(rule id.expand) simp
qed


subsection \<open>Probability monad\<close>

text \<open>We don't know of a sensible probability monad transformer, so we define the plain probability monad.\<close>

type_synonym 'a prob = "'a pmf"

lemma monad_prob [locale_witness]: "monad return_pmf bind_pmf"
by unfold_locales(simp_all add: bind_assoc_pmf bind_return_pmf bind_return_pmf')

lemma monad_prob_prob [locale_witness]: "monad_prob return_pmf bind_pmf bind_pmf"
proof
  show "bind_pmf p (\<lambda>_. m) = m" for p :: "'b pmf" and m :: "'a prob"
    by(rule bind_pmf_const)
  show "bind_pmf (return_pmf x) f = f x" for f :: "'b \<Rightarrow> 'a prob" and x by(rule bind_return_pmf)
  show "bind_pmf (bind_pmf p f) g = bind_pmf p (\<lambda>x. bind_pmf (f x) g)"
    for p :: "'b pmf" and f :: "'b \<Rightarrow> 'b pmf" and g :: "'b \<Rightarrow> 'a prob"
    by(rule bind_assoc_pmf)
  show "bind_pmf p (\<lambda>x. bind_pmf q (f x)) = bind_pmf q (\<lambda>y. bind_pmf p (\<lambda>x. f x y))"
    for p q :: "'b pmf" and f :: "'b \<Rightarrow> 'b \<Rightarrow> 'a prob" by(rule bind_commute_pmf)
  show "bind_pmf (bind_pmf p f) g = bind_pmf p (\<lambda>x. bind_pmf (f x) g)"
    for p :: "'b pmf" and f :: "'b \<Rightarrow> 'a prob" and g :: "'a \<Rightarrow> 'a prob"
    by(simp add: bind_assoc_pmf)
  show "bind_pmf m (\<lambda>y. bind_pmf p (f y)) = bind_pmf p (\<lambda>x. bind_pmf m (\<lambda>y. f y x))"
    for m :: "'a prob" and p :: "'b pmf" and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'a prob"
    by(rule bind_commute_pmf)
  show "bind_pmf p f = bind_pmf p g" if "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x" for p and f g :: "'b \<Rightarrow> 'a prob"
    using that by(blast intro: bind_pmf_cong)
qed

lemma monad_commute_prob [locale_witness]: "monad_commute return_pmf bind_pmf"
proof
  show "bind_pmf m (\<lambda>x. bind_pmf m' (f x)) = bind_pmf m' (\<lambda>y. bind_pmf m (\<lambda>x. f x y))"
    for m m' :: "'a prob" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a prob"
    by(rule bind_commute_pmf)
qed


subsection \<open>Resumption\<close>

text \<open>
  We cannot define a resumption monad transformer because the codatatype recursion would have to
  go through a type variable. If we plug in something like unbounded non-determinism, then the
  HOL type does not exist.
\<close>

codatatype ('o, 'i, 'a) resumption = is_Done: Done (result: 'a) | Pause ("output": 'o) (resume: "'i \<Rightarrow> ('o, 'i, 'a) resumption")

subsubsection \<open>Plain monad\<close>

definition return_resumption :: "'a \<Rightarrow> ('o, 'i, 'a) resumption"
where "return_resumption = Done"

primcorec bind_resumption :: "('o, 'i, 'a) resumption \<Rightarrow> ('a \<Rightarrow> ('o, 'i, 'a) resumption) \<Rightarrow> ('o, 'i, 'a) resumption"
where "bind_resumption m f = (if is_Done m then f (result m) else Pause (output m) (\<lambda>i. bind_resumption (resume m i) f))"

definition pause_resumption :: "'o \<Rightarrow> ('i \<Rightarrow> ('o, 'i, 'a) resumption) \<Rightarrow> ('o, 'i, 'a) resumption"
where "pause_resumption = Pause"

lemma is_Done_return_resumption [simp]: "is_Done (return_resumption x)"
by(simp add: return_resumption_def)

lemma result_return_resumption [simp]: "result (return_resumption x) = x"
by(simp add: return_resumption_def)

lemma monad_resumption [locale_witness]: "monad return_resumption bind_resumption"
proof
  show "bind_resumption (bind_resumption x f) g = bind_resumption x (\<lambda>y. bind_resumption (f y) g)"
    for x :: "('o, 'i, 'a) resumption" and f g
    by(coinduction arbitrary: x f g rule: resumption.coinduct_strong) auto
  show "bind_resumption (return_resumption x) f = f x" for x and f :: "'a \<Rightarrow> ('o, 'i, 'a) resumption"
    by(rule resumption.expand)(simp_all add: return_resumption_def)
  show "bind_resumption x return_resumption = x" for x :: "('o, 'i, 'a) resumption"
    by(coinduction arbitrary: x rule: resumption.coinduct_strong) auto
qed

lemma monad_resumption_resumption [locale_witness]:
  "monad_resumption return_resumption bind_resumption pause_resumption"
proof
  show "bind_resumption (pause_resumption out c) f = pause_resumption out (\<lambda>i. bind_resumption (c i) f)"
    for out c and f :: "'a \<Rightarrow> ('o, 'i, 'a) resumption"
    by(rule resumption.expand)(simp_all add: pause_resumption_def)
qed

subsection \<open>Unbounded non-determinism\<close>

abbreviation (input) return_set :: "'a \<Rightarrow> 'a set" where "return_set x \<equiv> {x}"
abbreviation (input) bind_set :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a set" where "bind_set \<equiv> UNION"
abbreviation (input) fail_set :: "'a set" where "fail_set \<equiv> {}"

lemma monad_set [locale_witness]: "monad return_set bind_set"
by unfold_locales auto

lemma monad_fail_set [locale_witness]: "monad_fail return_set bind_set fail_set"
by unfold_locales auto

lemma monad_lift_set [simp]: "monad_base.lift return_set bind_set  = image"
by(auto simp add: monad_base.lift_def o_def fun_eq_iff)

subsection \<open>Non-determinism transformer\<close>

datatype (plugins del: transfer) (phantom_nondetT: 'a, set_nondetT: 'm) nondetT = NondetT (run_nondet: 'm)
  for map: map_nondetT'
      rel: rel_nondetT'

text \<open>
  We define our own relator and mapper such that the phantom variable does not need any relation.
\<close>

lemma phantom_nondetT [simp]: "phantom_nondetT x = {}"
by(cases x) simp

context includes lifting_syntax begin

lemma rel_nondetT'_phantom: "rel_nondetT' A = rel_nondetT' top"
by(auto 4 4 intro: nondetT.rel_mono antisym nondetT.rel_mono_strong)

lemma map_nondetT'_phantom: "map_nondetT' f = map_nondetT' undefined"
by(auto 4 4 intro: nondetT.map_cong)

definition map_nondetT :: "('m \<Rightarrow> 'm') \<Rightarrow> ('a, 'm) nondetT \<Rightarrow> ('b, 'm') nondetT"
where "map_nondetT = map_nondetT' undefined"

definition rel_nondetT :: "('m \<Rightarrow> 'm' \<Rightarrow> bool) \<Rightarrow> ('a, 'm) nondetT \<Rightarrow> ('b, 'm') nondetT \<Rightarrow> bool"
where "rel_nondetT = rel_nondetT' top"

lemma rel_nondetTE:
  assumes "rel_nondetT M m m'"
  obtains x y where "m = NondetT x" "m' = NondetT y" "M x y"
using assms by(cases m; cases m'; simp add: rel_nondetT_def)

lemma rel_nondetT_simps [simp]: "rel_nondetT M (NondetT m) (NondetT m') \<longleftrightarrow> M m m'"
by(simp add: rel_nondetT_def)

lemma rel_nondetT_eq [relator_eq]: "rel_nondetT (=) = (=)"
by(auto simp add: fun_eq_iff rel_nondetT_def intro: nondetT.rel_refl_strong elim: nondetT.rel_cases)

lemma rel_nondetT_mono [relator_mono]: "rel_nondetT A \<le> rel_nondetT B" if "A \<le> B"
by(simp add: rel_nondetT_def nondetT.rel_mono that)

lemma rel_nondetT_distr [relator_distr]: "rel_nondetT A OO rel_nondetT B = rel_nondetT (A OO B)"
by(simp add: rel_nondetT_def nondetT.rel_compp[symmetric])

lemma rel_nondetT_Grp: "rel_nondetT (BNF_Def.Grp A f) = BNF_Def.Grp {x. set_nondetT x \<subseteq> A} (map_nondetT f)"
by(simp add: rel_nondetT_def rel_nondetT'_phantom[of "BNF_Def.Grp UNIV undefined", symmetric] nondetT.rel_Grp map_nondetT_def)

lemma NondetT_parametric [transfer_rule]: "(M ===> rel_nondetT M) NondetT NondetT"
by(simp add: rel_fun_def rel_nondetT_def)

lemma run_nondet_parametric [transfer_rule]: "(rel_nondetT M ===> M) run_nondet run_nondet"
by(auto simp add: rel_fun_def rel_nondetT_def elim: nondetT.rel_cases)

lemma case_nondetT_parametric [transfer_rule]:
  "((M ===> X) ===> rel_nondetT M ===> X) case_nondetT case_nondetT"
by(auto simp add: rel_fun_def rel_nondetT_def split: nondetT.split)

lemma rec_nondetT_parametric [transfer_rule]:
  "((M ===> X) ===> rel_nondetT M ===> X) rec_nondetT rec_nondetT"
by(auto simp add: rel_fun_def elim: rel_nondetTE)

end

context
  fixes return :: "('a multiset, 'm) return" 
  and bind :: "('a multiset, 'm) bind"
begin

definition return_nondet :: "('a, ('a, 'm) nondetT) return"
where "return_nondet x = NondetT (return {#x#})"

definition munionM :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
where "munionM m1 m2 = bind m1 (\<lambda>A. bind m2 (\<lambda>B. return (A + B)))"

definition mUnionM :: "'m multiset \<Rightarrow> 'm"
where "mUnionM = fold_mset munionM (return {#})"

definition bind_nondet :: "('a, ('a, 'm) nondetT) bind"
where "bind_nondet m f = NondetT (bind (run_nondet m) (\<lambda>A. mUnionM (image_mset (run_nondet \<circ> f) A)))"

definition fail_nondet :: "('a, 'm) nondetT fail"
where "fail_nondet = NondetT (return {#})"

definition alt_nondet :: "('a, 'm) nondetT alt"
where "alt_nondet m1 m2 = NondetT (bind (run_nondet m1) (\<lambda>A. bind (run_nondet m2) (\<lambda>B. return (A + B))))"

definition get_nondet :: "('s, 'm) get \<Rightarrow> ('s, ('a, 'm) nondetT) get"
where "get_nondet get f = NondetT (get (\<lambda>s. run_nondet (f s)))" for get

definition put_nondet :: "('s, 'm) put \<Rightarrow> ('s, ('a, 'm) nondetT) put"
where "put_nondet put s m = NondetT (put s (run_nondet m))" for put

definition ask_nondet :: "('r, 'm) ask \<Rightarrow> ('r, ('a, 'm) nondetT) ask"
where "ask_nondet ask f = NondetT (ask (\<lambda>r. run_nondet (f r)))"

text \<open>
  The canonical lift of sampling into @{typ "(_, _) nondetT"} does not satisfy @{const monad_prob},
  because sampling does not distribute over bind backwards. Intuitively, if we sample first,
  then the same sample is used in all non-deterministic choices. But if we sample later,
  each non-deterministic choice may sample a different value.
\<close>

lemma run_return_nondet [simp]: "run_nondet (return_nondet x) = return {#x#}"
by(simp add: return_nondet_def)

lemma run_bind_nondet [simp]:
  "run_nondet (bind_nondet m f) = bind (run_nondet m) (\<lambda>A. mUnionM (image_mset (run_nondet \<circ> f) A))"
by(simp add: bind_nondet_def)

lemma run_fail_nondet [simp]: "run_nondet fail_nondet = return {#}"
by(simp add: fail_nondet_def)

lemma run_alt_nondet [simp]:
  "run_nondet (alt_nondet m1 m2) = bind (run_nondet m1) (\<lambda>A. bind (run_nondet m2) (\<lambda>B. return (A + B)))"
by(simp add: alt_nondet_def)

lemma run_get_nondet [simp]: "run_nondet (get_nondet get f) = get (\<lambda>s. run_nondet (f s))" for get
by(simp add: get_nondet_def)

lemma run_put_nondet [simp]: "run_nondet (put_nondet put s m) = put s (run_nondet m)" for put
by(simp add: put_nondet_def)

lemma run_ask_nondet [simp]: "run_nondet (ask_nondet ask f) = ask (\<lambda>r. run_nondet (f r))" for ask
by(simp add: ask_nondet_def)

text \<open>
  Because of multisets, we must assume that the inner monad is commutative. If we used finite
  sets, then we would even need that the effects of the inner monad can be duplicated.
\<close>
context assumes "monad_commute return bind" begin

interpretation monad_commute return bind by fact

interpretation comp_fun_commute munionM
apply(unfold_locales)
apply(simp add: fun_eq_iff bind_assoc return_bind munionM_def)
apply(subst bind_commute)
apply(simp add: union_ac)
done

lemma mUnionM_empty [simp]: "mUnionM {#} = return {#}"
by(simp add: mUnionM_def)

lemma mUnionM_add_mset [simp]: "mUnionM (add_mset x M) = munionM x (mUnionM M)"
by(simp add: mUnionM_def)

lemma munionM_return_empty1 [simp]: "munionM (return {#}) x = x"
by(simp add: munionM_def return_bind bind_return)

lemma munionM_return_empty2 [simp]: "munionM x (return {#}) = x"
by(simp add: munionM_def return_bind bind_return)

lemma munionM_return_return [simp]: "munionM (return A) (return B) = return (A + B)"
by(simp add: munionM_def return_bind)

lemma munionM_assoc: "munionM (munionM x y) z = munionM x (munionM y z)"
by(simp add: munionM_def bind_assoc return_bind add.assoc)

lemma munionM_commute: "munionM x y = munionM y x"
unfolding munionM_def by(subst bind_commute)(simp add: add.commute)

lemma munionM_mUnionM1: "munionM (mUnionM A) x = fold_mset munionM x A"
by(induction A arbitrary: x)(simp_all add: munionM_assoc)

lemma munionM_mUnionM2: "munionM x (mUnionM A) = fold_mset munionM x A"
by(subst munionM_commute)(rule munionM_mUnionM1)

lemma mUnionM_add [simp]: "mUnionM (A + B) = munionM (mUnionM A) (mUnionM B)"
by(subst munionM_mUnionM2)(simp add: mUnionM_def)

lemma mUnionM_return [simp]: "mUnionM (image_mset (\<lambda>x. return {#x#}) A) = return A"
by(induction A) simp_all

lemma bind_munionM: 
  assumes "\<And>A B. f (A + B) = bind (f A) (\<lambda>x. bind (f B) (\<lambda>y. return (x + y)))"
  shows "bind (munionM m m') f = munionM (bind m f) (bind m' f)"
apply(simp add: munionM_def bind_assoc return_bind assms)
apply(subst (2) bind_commute)
apply simp
done

lemma monad_nondetT [locale_witness]: "monad return_nondet bind_nondet"
proof
  have eq: "bind (mUnionM (image_mset (run_nondet \<circ> f) y)) (\<lambda>A. mUnionM (image_mset (run_nondet \<circ> g) A)) =
         mUnionM (image_mset (run_nondet \<circ> (\<lambda>y. bind_nondet (f y) g)) y)" for y f g
    apply(induction y)
     apply(simp_all add: return_bind)
    apply(subst bind_munionM; simp add: munionM_def o_def)
    done

  show "bind_nondet (bind_nondet x f) g = bind_nondet x (\<lambda>y. bind_nondet (f y) g)" for x f g
    by(rule nondetT.expand)(simp add: bind_assoc eq)
  show "bind_nondet (return_nondet x) f = f x" for x f
    by(rule nondetT.expand)(simp add: return_bind)
  show "bind_nondet x return_nondet = x" for x
    by(rule nondetT.expand)(simp add: bind_return o_def)
qed

lemma monad_fail_nondetT [locale_witness]: "monad_fail return_nondet bind_nondet fail_nondet"
proof
  show "bind_nondet fail_nondet f = fail_nondet" for f
    by(rule nondetT.expand)(simp add: return_bind)
qed

lemma monad_alt_nondetT [locale_witness]: "monad_alt return_nondet bind_nondet alt_nondet"
proof
  show "alt_nondet (alt_nondet m1 m2) m3 = alt_nondet m1 (alt_nondet m2 m3)" for m1 m2 m3
    by(rule nondetT.expand)(simp add: bind_assoc return_bind add.assoc)
  show "bind_nondet (alt_nondet m m') f = alt_nondet (bind_nondet m f) (bind_nondet m' f)" for m m' f
    apply(rule nondetT.expand)
    apply(simp add: bind_assoc return_bind)
    apply(subst (2) bind_commute)
    apply(simp add: munionM_def)
    done
qed

lemma monad_fail_alt_nondetT [locale_witness]:
  "monad_fail_alt return_nondet bind_nondet fail_nondet alt_nondet"
proof
  show "alt_nondet fail_nondet m = m" for  m
    by(rule nondetT.expand)(simp add: return_bind bind_return)
  show "alt_nondet m fail_nondet = m" for m
    by(rule nondetT.expand)(simp add: return_bind bind_return)
qed

lemma monad_state_nondetT [locale_witness]:
  \<comment> \<open>It's not really sensible to assume a commutative state monad, but let's prove it anyway ...\<close>
  fixes get put
  assumes "monad_state return bind get put"
  shows "monad_state return_nondet bind_nondet (get_nondet get) (put_nondet put)"
proof -
  interpret monad_state return bind get put by fact
  show ?thesis
  proof
    show "put_nondet put s (get_nondet get f) = put_nondet put s (f s)" for s f
      by(rule nondetT.expand)(simp add: put_get)
    show "get_nondet get (\<lambda>s. get_nondet get (f s)) = get_nondet get (\<lambda>s. f s s)" for f
      by(rule nondetT.expand)(simp add: get_get)
    show "put_nondet put s (put_nondet put s' m) = put_nondet put s' m" for s s' m
      by(rule nondetT.expand)(simp add: put_put)
    show "get_nondet get (\<lambda>s. put_nondet put s m) = m" for m
      by(rule nondetT.expand)(simp add: get_put)
    show "get_nondet get (\<lambda>_. m) = m" for m
      by(rule nondetT.expand)(simp add: get_const)
    show "bind_nondet (get_nondet get f) g = get_nondet get (\<lambda>s. bind_nondet (f s) g)" for f g
      by(rule nondetT.expand)(simp add: bind_get)
    show "bind_nondet (put_nondet put s m) f = put_nondet put s (bind_nondet m f)" for s m f
      by(rule nondetT.expand)(simp add: bind_put)
  qed
qed

lemma monad_reader_nondetT [locale_witness]:
  assumes "monad_reader return bind ask"
  shows "monad_reader return_nondet bind_nondet (ask_nondet ask)"
proof
  interpret monad_reader return bind ask by fact
  show "ask_nondet ask (\<lambda>r. ask_nondet ask (f r)) = ask_nondet ask (\<lambda>r. f r r)" for f
    by(rule nondetT.expand)(simp add: ask_ask)
  show "ask_nondet ask (\<lambda>_. m) = m" for m
    by(rule nondetT.expand)(simp add: ask_const)
  show "bind_nondet (ask_nondet ask f) g = ask_nondet ask (\<lambda>r. bind_nondet (f r) g)" for f g
    by(rule nondetT.expand)(simp add: bind_ask)
  have *: "mUnionM (image_mset (\<lambda>x. ask (\<lambda>r. run_nondet (f x r))) A) = 
    ask (\<lambda>r. mUnionM (image_mset (\<lambda>x. run_nondet (f x r)) A))" for f and A
    by(induction A)(simp_all add: ask_const munionM_def bind_ask bind_ask2 ask_ask)
  show "bind_nondet m (\<lambda>x. ask_nondet ask (f x)) = ask_nondet ask (\<lambda>r. bind_nondet m (\<lambda>x. f x r))" for f m
    by(rule nondetT.expand)(simp add: bind_ask2[symmetric] o_def *)
qed

end

end

subsection \<open>State transformer\<close>

datatype ('s, 'm) stateT = StateT (run_state: "'s \<Rightarrow> 'm")
  for rel: rel_stateT'

text \<open>
  We define a more general relator for @{typ "(_, _) stateT"} than the one generated
  by the datatype package such that we can also show parametricity in the state.
\<close>

context includes lifting_syntax begin

definition rel_stateT :: "('s \<Rightarrow> 's' \<Rightarrow> bool) \<Rightarrow> ('m \<Rightarrow> 'm' \<Rightarrow> bool) \<Rightarrow> ('s, 'm) stateT \<Rightarrow> ('s', 'm') stateT \<Rightarrow> bool"
where "rel_stateT S M m m' \<longleftrightarrow> (S ===> M) (run_state m) (run_state m')"

lemma rel_stateT_eq [relator_eq]: "rel_stateT (=) (=) = (=)"
by(auto simp add: rel_stateT_def fun_eq_iff rel_fun_eq intro: stateT.expand)

lemma rel_stateT_mono [relator_mono]: "\<lbrakk> S' \<le> S; M \<le> M' \<rbrakk> \<Longrightarrow> rel_stateT S M \<le> rel_stateT S' M'"
by(rule predicate2I)(simp add: rel_stateT_def fun_mono[THEN predicate2D]) 

lemma StateT_parametric [transfer_rule]: "((S ===> M) ===> rel_stateT S M) StateT StateT"
by(auto simp add: rel_stateT_def)

lemma run_state_parametric [transfer_rule]: "(rel_stateT S M ===> S ===> M) run_state run_state"
by(auto simp add: rel_stateT_def)

lemma case_stateT_parametric [transfer_rule]: 
  "(((S ===> M) ===> A) ===> rel_stateT S M ===> A) case_stateT case_stateT"
by(auto 4 3 split: stateT.split simp add: rel_stateT_def del: rel_funI intro!: rel_funI dest: rel_funD)

lemma rec_stateT_parametric [transfer_rule]: 
  "(((S ===> M) ===> A) ===> rel_stateT S M ===> A) rec_stateT rec_stateT"
apply(rule rel_funI)+
subgoal for \<dots> m m' by(cases m; cases m')(auto 4 3 simp add: rel_stateT_def del: rel_funI intro!: rel_funI dest: rel_funD)
done

end

subsubsection \<open>Plain monad, get, and put\<close>

context 
  fixes return :: "('a \<times> 's, 'm) return"
  and bind :: "('a \<times> 's, 'm) bind"
begin

primrec bind_state :: "('a, ('s, 'm) stateT) bind"
where "bind_state (StateT x) f = StateT (\<lambda>s. bind (x s) (\<lambda>(a, s'). run_state (f a) s'))"

definition return_state :: "('a, ('s, 'm) stateT) return"
where "return_state x = StateT (\<lambda>s. return (x, s))"

definition get_state :: "('s, ('s, 'm) stateT) get"
where "get_state f = StateT (\<lambda>s. run_state (f s) s)"

primrec put_state :: "('s, ('s, 'm) stateT) put"
where "put_state s (StateT f) = StateT (\<lambda>_. f s)"

lemma run_put_state [simp]: "run_state (put_state s m) s' = run_state m s"
by(cases m) simp

lemma run_get_state [simp]: "run_state (get_state f) s = run_state (f s) s"
by(simp add: get_state_def)

lemma run_bind_state [simp]:
  "run_state (bind_state x f) s = bind (run_state x s) (\<lambda>(a, s'). run_state (f a) s')"
by(cases x)(simp)

lemma run_return_state [simp]:
  "run_state (return_state x) s = return (x, s)"
by(simp add: return_state_def)

context
  assumes monad: "monad return bind"
begin

interpretation monad return bind by(fact monad)

lemma monad_stateT [locale_witness]: "monad return_state bind_state" (is "monad ?return ?bind")
proof
  show "?bind (?bind x f) g = ?bind x (\<lambda>x. ?bind (f x) g)" for x and f g :: "'a \<Rightarrow> ('s, 'm) stateT"
    by(rule stateT.expand ext)+(simp add: bind_assoc split_def)
  show "?bind (?return x) f = f x" for f :: "'a \<Rightarrow> ('s, 'm) stateT" and x
    by(rule stateT.expand ext)+(simp add: return_bind)
  show "?bind x ?return = x" for x
    by(rule stateT.expand ext)+(simp add: bind_return)
qed

lemma monad_state_stateT [locale_witness]:
  "monad_state return_state bind_state get_state put_state"
proof
  show "put_state s (get_state f) = put_state s (f s)" for f :: "'s \<Rightarrow> ('s, 'm) stateT" and s :: "'s"
    by(rule stateT.expand)(simp add: get_state_def fun_eq_iff)
  show "get_state (\<lambda>s. get_state (f s)) = get_state (\<lambda>s. f s s)" for f :: "'s \<Rightarrow> 's \<Rightarrow> ('s, 'm) stateT"
    by(rule stateT.expand)(simp add: fun_eq_iff)
  show "put_state s (put_state s' m) = put_state s' m" for s s' :: 's and m :: "('s, 'm) stateT"
    by(rule stateT.expand)(simp add: fun_eq_iff)
  show "get_state (\<lambda>s :: 's. put_state s m) = m" for m :: "('s, 'm) stateT"
    by(rule stateT.expand)(simp add: fun_eq_iff)  
  show "get_state (\<lambda>_. m) = m" for m :: "('s, 'm) stateT"
    by(rule stateT.expand)(simp add: fun_eq_iff)
  show "bind_state (get_state f) g = get_state (\<lambda>s. bind_state (f s) g)" for f g
    by(rule stateT.expand)(simp add: fun_eq_iff)
  show "bind_state (put_state s m) f = put_state s (bind_state m f)" for s :: 's and m f
    by(rule stateT.expand)(simp add: fun_eq_iff)
qed

end

text \<open>
  We cannot define a generic lifting operation for state like in Haskell.
  If we separate the monad type variable from the element type variable, then
  @{text lift} should have type @{text "'a 'm => (('a \<times> 's) 'm) stateT"}, but this means
  that the type of results must change, which does not work for monomorphic monads.

  Instead, we must lift all operations individually. @{text "lift_definition"} does not work
  because the monad transformer type is typically larger than the base type, but
  @{text "lift_definition"} only works if the lifted type is no bigger.
\<close>

subsubsection \<open>Failure\<close>

context
  fixes fail :: "'m fail"
begin

definition fail_state :: "('s, 'm) stateT fail"
where "fail_state = StateT (\<lambda>s. fail)"

lemma run_fail_state [simp]: "run_state fail_state s = fail"
by(simp add: fail_state_def)

lemma monad_fail_stateT [locale_witness]:
  assumes "monad_fail return bind fail"
  shows "monad_fail return_state bind_state fail_state" (is "monad_fail ?return ?bind ?fail")
proof -
  interpret monad_fail return bind fail by(fact assms)
  have "?bind ?fail f = ?fail" for f by(rule stateT.expand)(simp add: fun_eq_iff fail_bind)
  then show ?thesis by unfold_locales
qed

notepad begin
  text \<open>
    @{text catch} cannot be lifted through the state monad according to @{term monad_catch_state}
   because there is now way to communicate the state updates to the handler.
  \<close>
  fix catch :: "'m catch"
  assume "monad_catch return bind fail catch"
  then interpret monad_catch return bind fail catch .

  define catch_state :: "('s, 'm) stateT catch" where
    "catch_state m1 m2 = StateT (\<lambda>s. catch (run_state m1 s) (run_state m2 s))" for m1 m2
  have "monad_catch return_state bind_state fail_state catch_state"
    by(unfold_locales; rule stateT.expand; simp add: fun_eq_iff catch_state_def catch_return catch_fail catch_fail2 catch_assoc)
end

end

subsubsection \<open>Reader\<close>

context
  fixes ask :: "('r, 'm) ask"
begin

definition ask_state :: "('r, ('s, 'm) stateT) ask"
where "ask_state f = StateT (\<lambda>s. ask (\<lambda>r. run_state (f r) s))"

lemma run_ask_state [simp]:
  "run_state (ask_state f) s = ask (\<lambda>r. run_state (f r) s)"
by(simp add: ask_state_def)

lemma monad_reader_stateT [locale_witness]:
  assumes "monad_reader return bind ask"
  shows "monad_reader return_state bind_state ask_state"
proof -
  interpret monad_reader return bind ask by(fact assms)
  show ?thesis
  proof
    show "ask_state (\<lambda>r. ask_state (f r)) = ask_state (\<lambda>r. f r r)" for f :: "'r \<Rightarrow> 'r \<Rightarrow> ('s, 'm) stateT"
      by(rule stateT.expand)(simp add: fun_eq_iff ask_ask)
    show "ask_state (\<lambda>_. x) = x" for x
      by(rule stateT.expand)(simp add: fun_eq_iff ask_const)
    show "bind_state (ask_state f) g = ask_state (\<lambda>r. bind_state (f r) g)" for f g
      by(rule stateT.expand)(simp add: fun_eq_iff bind_ask)
    show "bind_state m (\<lambda>x. ask_state (f x)) = ask_state (\<lambda>r. bind_state m (\<lambda>x. f x r))" for m f
      by(rule stateT.expand)(simp add: fun_eq_iff bind_ask2 split_def)
  qed
qed

lemma monad_reader_state_stateT [locale_witness]:
  assumes "monad_reader return bind ask"
  shows "monad_reader_state return_state bind_state ask_state get_state put_state"
proof -
  interpret monad_reader return bind ask by(fact assms)
  show ?thesis
  proof
    show "ask_state (\<lambda>r. get_state (f r)) = get_state (\<lambda>s. ask_state (\<lambda>r. f r s))" for f
      by(rule stateT.expand)(simp add: fun_eq_iff)
    show "put_state m (ask_state f) = ask_state (\<lambda>r. put_state m (f r))" for m f
      by(rule stateT.expand)(simp add: fun_eq_iff)
  qed
qed

end

subsubsection \<open>Probability\<close>

context
  fixes sample :: "('p, 'm) sample"
begin

definition sample_state :: "('p, ('s, 'm) stateT) sample"
where "sample_state p f = StateT (\<lambda>s. sample p (\<lambda>x. run_state (f x) s))"

lemma run_sample_state [simp]:
  "run_state (sample_state p f) s = sample p (\<lambda>x. run_state (f x) s)"
by(simp add: sample_state_def)

context
  assumes "monad_prob return bind sample"
begin

interpretation monad_prob return bind sample by(fact)

lemma monad_prob_stateT [locale_witness]: "monad_prob return_state bind_state sample_state"
proof
  show "sample_state p (\<lambda>_. x) = x" for p x
    by(rule stateT.expand)(simp add: fun_eq_iff sample_const)
  show "sample_state (return_pmf x) f = f x" for f x
    by(rule stateT.expand)(simp add: fun_eq_iff sample_return_pmf)
  show "sample_state (bind_pmf p f) g = sample_state p (\<lambda>x. sample_state (f x) g)" for p f g
    by(rule stateT.expand)(simp add: fun_eq_iff sample_bind_pmf)
  show "sample_state p (\<lambda>x. sample_state q (f x)) = sample_state q (\<lambda>y. sample_state p (\<lambda>x. f x y))" for p q f
    by(rule stateT.expand)(auto simp add: fun_eq_iff intro: sample_commute)
  show "bind_state (sample_state p f) g = sample_state p (\<lambda>x. bind_state (f x) g)" for p f g
    by(rule stateT.expand)(simp add: fun_eq_iff bind_sample1)
  show "bind_state m (\<lambda>y. sample_state p (f y)) = sample_state p (\<lambda>x. bind_state m (\<lambda>y. f y x))" for m p f
    by(rule stateT.expand)(simp add: fun_eq_iff bind_sample2 split_def)
  show "sample_state p f = sample_state p g" if "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x" for p f g
    by(rule stateT.expand)(auto simp add: fun_eq_iff intro!: sample_cong dest: that)
qed

lemma monad_state_prob_stateT [locale_witness]:
  "monad_state_prob return_state bind_state get_state put_state sample_state"
proof
  show "sample_state p (\<lambda>x. get_state (f x)) = get_state (\<lambda>s. sample_state p (\<lambda>x. f x s))" for p f
    by(rule stateT.expand)(simp add: fun_eq_iff)
qed

end

end

subsubsection \<open>Writer\<close>

context
  fixes tell :: "('w, 'm) tell"
begin

definition tell_state :: "('w, ('s, 'm) stateT) tell"
where "tell_state w m = StateT (\<lambda>s. tell w (run_state m s))"

lemma run_tell_state [simp]: "run_state (tell_state w m) s = tell w (run_state m s)"
by(simp add: tell_state_def)

lemma monad_writer_stateT [locale_witness]:
  assumes "monad_writer return bind tell"
  shows "monad_writer return_state bind_state tell_state"
proof -
  interpret monad_writer return bind tell by(fact assms)
  show ?thesis
  proof
    show "bind_state (tell_state w m) f = tell_state w (bind_state m f)" for w m f
      by(rule stateT.expand)(simp add: bind_tell fun_eq_iff)
  qed
qed

end

subsubsection \<open>Non-determinism\<close>

context
  fixes alt :: "'m alt"
begin

definition alt_state :: "('s, 'm) stateT alt"
where "alt_state m1 m2 = StateT (\<lambda>s. alt (run_state m1 s) (run_state m2 s))"

lemma run_alt_state [simp]: "run_state (alt_state m1 m2) s = alt (run_state m1 s) (run_state m2 s)"
by(simp add: alt_state_def)

lemma monad_alt_stateT [locale_witness]:
  assumes "monad_alt return bind alt"
  shows "monad_alt return_state bind_state alt_state"
proof -
  interpret monad_alt return bind alt by fact
  show ?thesis
  proof
    show "alt_state (alt_state m1 m2) m3 = alt_state m1 (alt_state m2 m3)" for m1 m2 m3
      by(rule stateT.expand)(simp add: alt_assoc fun_eq_iff)
    show "bind_state (alt_state m m') f = alt_state (bind_state m f) (bind_state m' f)" for m m' f
      by(rule stateT.expand)(simp add: bind_alt1 fun_eq_iff)
  qed
qed

lemma monad_fail_alt_stateT [locale_witness]:
  fixes fail
  assumes "monad_fail_alt return bind fail alt"
  shows "monad_fail_alt return_state bind_state (fail_state fail) alt_state"
proof -
  interpret monad_fail_alt return bind fail alt by fact
  show ?thesis
  proof
    show  "alt_state (fail_state fail) m = m" for m
      by(rule stateT.expand)(simp add: fun_eq_iff alt_fail1)
    show "alt_state m (fail_state fail) = m" for m
      by(rule stateT.expand)(simp add: fun_eq_iff alt_fail2)
  qed
qed

end

subsubsection \<open>Resumption\<close>

context
  fixes pause :: "('o, 'i, 'm) pause"
begin

definition pause_state :: "('o, 'i, ('s, 'm) stateT) pause"
where "pause_state out c = StateT (\<lambda>s. pause out (\<lambda>i. run_state (c i) s))"

lemma run_pause_state [simp]:
  "run_state (pause_state out c) s = pause out (\<lambda>i. run_state (c i) s)"
by(simp add: pause_state_def)

lemma monad_resumption_stateT [locale_witness]:
  assumes "monad_resumption return bind pause"
  shows "monad_resumption return_state bind_state pause_state"
proof -
  interpret monad_resumption return bind pause by fact
  show ?thesis
  proof
    show "bind_state (pause_state out c) f = pause_state out (\<lambda>i. bind_state (c i) f)" for out c f
      by(rule stateT.expand)(simp add: fun_eq_iff bind_pause)
  qed
qed

end

end

subsubsection \<open>Parametricity\<close>

context includes lifting_syntax begin

lemma return_state_parametric [transfer_rule]:
  "((rel_prod A S ===> M) ===> A ===> rel_stateT S M) return_state return_state"
unfolding return_state_def by transfer_prover

lemma bind_state_parametric [transfer_rule]:
  "((M ===> (rel_prod A S ===> M) ===> M) ===> rel_stateT S M ===> (A ===> rel_stateT S M) ===> rel_stateT S M)
   bind_state bind_state"
unfolding bind_state_def by transfer_prover

lemma get_state_parametric [transfer_rule]:
  "((S ===> rel_stateT S M) ===> rel_stateT S M) get_state get_state"
unfolding get_state_def by transfer_prover

lemma put_state_parametric [transfer_rule]:
  "(S ===> rel_stateT S M ===> rel_stateT S M) put_state put_state"
unfolding put_state_def by transfer_prover

lemma fail_state_parametric [transfer_rule]: "(M ===> rel_stateT S M) fail_state fail_state"
unfolding fail_state_def by transfer_prover

lemma ask_state_parametric [transfer_rule]:
  "(((R ===> M) ===> M) ===> (R ===> rel_stateT S M) ===> rel_stateT S M) ask_state ask_state"
unfolding ask_state_def by transfer_prover

lemma sample_state_parametric [transfer_rule]:
  "((rel_pmf P ===> (P ===> M) ===> M) ===> rel_pmf P ===> (P ===> rel_stateT S M) ===> rel_stateT S M)
   sample_state sample_state"
unfolding sample_state_def by transfer_prover

lemma tell_state_parametric [transfer_rule]:
  "((W ===> M ===> M) ===> W ===> rel_stateT S M ===> rel_stateT S M)
   tell_state tell_state"
unfolding tell_state_def by transfer_prover

lemma alt_state_parametric [transfer_rule]:
  "((M ===> M ===> M) ===> rel_stateT S M ===> rel_stateT S M ===> rel_stateT S M)
   alt_state alt_state"
unfolding alt_state_def by transfer_prover

lemma pause_state_parametric [transfer_rule]:
  "((Out ===> (In ===> M) ===> M) ===> Out ===> (In ===> rel_stateT S M) ===> rel_stateT S M)
   pause_state pause_state"
unfolding pause_state_def by transfer_prover

end

subsection \<open>Failure and exception monad transformer\<close>

text \<open>
  The phantom type variable @{typ 'a} is needed to avoid hidden polymorphism when overloading the
  monad operations for the failure monad transformer.
\<close>

datatype (plugins del: transfer) (phantom_optionT: 'a, set_optionT: 'm) optionT = OptionT (run_option: 'm)
  for rel: rel_optionT' 
      map: map_optionT'

text \<open>
  We define our own relator and mapper such that the phantom variable does not need any relation.
\<close>

lemma phantom_optionT [simp]: "phantom_optionT x = {}"
by(cases x) simp

context includes lifting_syntax begin

lemma rel_optionT'_phantom: "rel_optionT' A = rel_optionT' top"
by(auto 4 4 intro: optionT.rel_mono antisym optionT.rel_mono_strong)

lemma map_optionT'_phantom: "map_optionT' f = map_optionT' undefined"
by(auto 4 4 intro: optionT.map_cong)

definition map_optionT :: "('m \<Rightarrow> 'm') \<Rightarrow> ('a, 'm) optionT \<Rightarrow> ('b, 'm') optionT"
where "map_optionT = map_optionT' undefined"

definition rel_optionT :: "('m \<Rightarrow> 'm' \<Rightarrow> bool) \<Rightarrow> ('a, 'm) optionT \<Rightarrow> ('b, 'm') optionT \<Rightarrow> bool"
where "rel_optionT = rel_optionT' top"

lemma rel_optionTE:
  assumes "rel_optionT M m m'"
  obtains x y where "m = OptionT x" "m' = OptionT y" "M x y"
using assms by(cases m; cases m'; simp add: rel_optionT_def)

lemma rel_optionT_simps [simp]: "rel_optionT M (OptionT m) (OptionT m') \<longleftrightarrow> M m m'"
by(simp add: rel_optionT_def)

lemma rel_optionT_eq [relator_eq]: "rel_optionT (=) = (=)"
by(auto simp add: fun_eq_iff rel_optionT_def intro: optionT.rel_refl_strong elim: optionT.rel_cases)

lemma rel_optionT_mono [relator_mono]: "rel_optionT A \<le> rel_optionT B" if "A \<le> B"
by(simp add: rel_optionT_def optionT.rel_mono that)

lemma rel_optionT_distr [relator_distr]: "rel_optionT A OO rel_optionT B = rel_optionT (A OO B)"
by(simp add: rel_optionT_def optionT.rel_compp[symmetric])

lemma rel_optionT_Grp: "rel_optionT (BNF_Def.Grp A f) = BNF_Def.Grp {x. set_optionT x \<subseteq> A} (map_optionT f)"
by(simp add: rel_optionT_def rel_optionT'_phantom[of "BNF_Def.Grp UNIV undefined", symmetric] optionT.rel_Grp map_optionT_def)

lemma OptionT_parametric [transfer_rule]: "(M ===> rel_optionT M) OptionT OptionT"
by(simp add: rel_fun_def rel_optionT_def)

lemma run_option_parametric [transfer_rule]: "(rel_optionT M ===> M) run_option run_option"
by(auto simp add: rel_fun_def rel_optionT_def elim: optionT.rel_cases)

lemma case_optionT_parametric [transfer_rule]:
  "((M ===> X) ===> rel_optionT M ===> X) case_optionT case_optionT"
by(auto simp add: rel_fun_def rel_optionT_def split: optionT.split)

lemma rec_optionT_parametric [transfer_rule]:
  "((M ===> X) ===> rel_optionT M ===> X) rec_optionT rec_optionT"
by(auto simp add: rel_fun_def elim: rel_optionTE)

end

subsubsection \<open>Plain monad, failure, and exceptions\<close>

context
  fixes return :: "('a option, 'm) return"
  and bind :: "('a option, 'm) bind"
begin

definition return_option :: "('a, ('a, 'm) optionT) return"
where "return_option x = OptionT (return (Some x))"

primrec bind_option :: "('a, ('a, 'm) optionT) bind"
where [code_unfold, monad_unfold]:
  "bind_option (OptionT x) f = 
   OptionT (bind x (\<lambda>x. case x of None \<Rightarrow> return (None :: 'a option) | Some y \<Rightarrow> run_option (f y)))"

definition fail_option :: "('a, 'm) optionT fail"
where [code_unfold, monad_unfold]: "fail_option = OptionT (return None)"

definition catch_option :: "('a, 'm) optionT catch"
where "catch_option m h = OptionT (bind (run_option m) (\<lambda>x. if x = None then run_option h else return x))"

lemma run_bind_option:
  "run_option (bind_option x f) = bind (run_option x) (\<lambda>x. case x of None \<Rightarrow> return None | Some y \<Rightarrow> run_option (f y))"
by(cases x) simp

lemma run_return_option [simp]: "run_option (return_option x) = return (Some x)"
by(simp add: return_option_def)

lemma run_fail_option [simp]: "run_option fail_option = return None"
by(simp add: fail_option_def)

lemma run_catch_option [simp]: 
  "run_option (catch_option m1 m2) = bind (run_option m1) (\<lambda>x. if x = None then run_option m2 else return x)"
by(simp add: catch_option_def)

context
  assumes monad: "monad return bind"
begin

interpretation monad return bind by(rule monad)

lemma monad_optionT [locale_witness]: "monad return_option bind_option" (is "monad ?return ?bind")
proof
  show "?bind (?bind x f) g = ?bind x (\<lambda>x. ?bind (f x) g)"  for x f g
    by(rule optionT.expand)(auto simp add: bind_assoc run_bind_option return_bind intro!: arg_cong2[where f=bind] split: option.split)
  show "?bind (?return x) f = f x" for f x
    by(rule optionT.expand)(simp add: run_bind_option return_bind return_option_def)
  show "?bind x ?return = x" for x
    by(rule optionT.expand)(simp add: run_bind_option option.case_distrib[symmetric] case_option_id bind_return cong del: option.case_cong)
qed

lemma monad_fail_optionT [locale_witness]:
  "monad_fail return_option bind_option fail_option"
proof
  show "bind_option fail_option f = fail_option" for f
    by(rule optionT.expand)(simp add: run_bind_option return_bind)
qed

lemma monad_catch_optionT [locale_witness]:
  "monad_catch return_option bind_option fail_option catch_option"
proof
  show "catch_option (return_option x) m = return_option x" for x m
    by(rule optionT.expand)(simp add: return_bind)
  show "catch_option fail_option m = m" for m
    by(rule optionT.expand)(simp add: return_bind)
  show "catch_option m fail_option = m" for m
    by(rule optionT.expand)(simp add: bind_return if_distrib[where f="return", symmetric] cong del: if_weak_cong)
   show "catch_option (catch_option m m') m'' = catch_option m (catch_option m' m'')" for m m' m''
    by(rule optionT.expand)(auto simp add: bind_assoc fun_eq_iff return_bind intro!: arg_cong2[where f=bind])
qed

end

subsubsection \<open>Reader\<close>

context
  fixes ask :: "('r, 'm) ask"
begin

definition ask_option :: "('r, ('a, 'm) optionT) ask" 
where [code_unfold, monad_unfold]: "ask_option f = OptionT (ask (\<lambda>r. run_option (f r)))"

lemma run_ask_option [simp]: "run_option (ask_option f) = ask (\<lambda>r. run_option (f r))"
by(simp add: ask_option_def)

lemma monad_reader_optionT [locale_witness]:
  assumes "monad_reader return bind ask"
  shows "monad_reader return_option bind_option ask_option"
proof -
  interpret monad_reader return bind ask by(fact assms)
  show ?thesis
  proof
    show "ask_option (\<lambda>r. ask_option (f r)) = ask_option (\<lambda>r. f r r)" for f
      by(rule optionT.expand)(simp add: ask_ask)
    show "ask_option (\<lambda>_. x) = x" for x
      by(rule optionT.expand)(simp add: ask_const)
    show "bind_option (ask_option f) g = ask_option (\<lambda>r. bind_option (f r) g)" for f g
      by(rule optionT.expand)(simp add: bind_ask run_bind_option)
    show "bind_option m (\<lambda>x. ask_option (f x)) = ask_option (\<lambda>r. bind_option m (\<lambda>x. f x r))" for m f
      by(rule optionT.expand)(auto simp add: bind_ask2[symmetric] run_bind_option ask_const del: ext intro!: arg_cong2[where f=bind] ext split: option.split)
  qed
qed

end

subsubsection \<open>State\<close>

context
  fixes get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
begin

definition get_option :: "('s, ('a, 'm) optionT) get"
where "get_option f = OptionT (get (\<lambda>s. run_option (f s)))"

primrec put_option :: "('s, ('a, 'm) optionT) put"
where "put_option s (OptionT m) = OptionT (put s m)"

lemma run_get_option [simp]:
  "run_option (get_option f) = get (\<lambda>s. run_option (f s))"
by(simp add: get_option_def)

lemma run_put_option [simp]:
  "run_option (put_option s m) = put s (run_option m)"
by(cases m)(simp)

context
  assumes state: "monad_state return bind get put"
begin

interpretation monad_state return bind get put by(fact state)

lemma monad_state_optionT [locale_witness]:
  "monad_state return_option bind_option get_option put_option"
proof
  show "put_option s (get_option f) = put_option s (f s)" for s f
    by(rule optionT.expand)(simp add: put_get)
  show "get_option (\<lambda>s. get_option (f s)) = get_option (\<lambda>s. f s s)" for f
    by(rule optionT.expand)(simp add: get_get)
  show "put_option s (put_option s' m) = put_option s' m" for s s' m
    by(rule optionT.expand)(simp add: put_put)
  show "get_option (\<lambda>s. put_option s m) = m" for m
    by(rule optionT.expand)(simp add: get_put)
  show "get_option (\<lambda>_. m) = m" for m
    by(rule optionT.expand)(simp add: get_const)
  show "bind_option (get_option f) g = get_option (\<lambda>s. bind_option (f s) g)" for f g
    by(rule optionT.expand)(simp add: bind_get run_bind_option)
  show "bind_option (put_option s m) f = put_option s (bind_option m f)" for s m f
    by(rule optionT.expand)(simp add: bind_put run_bind_option)
qed

lemma monad_catch_state_optionT [locale_witness]:
  "monad_catch_state return_option bind_option fail_option catch_option get_option put_option"
proof
  show "catch_option (get_option f) m = get_option (\<lambda>s. catch_option (f s) m)" for f m
    by(rule optionT.expand)(simp add: bind_get)
  show "catch_option (put_option s m) m' = put_option s (catch_option m m')" for s m m'
    by(rule optionT.expand)(simp add: bind_put)
qed

end

end

subsubsection \<open>Probability\<close>

context
  fixes sample :: "('p, 'm) sample"
begin

definition sample_option :: "('p, ('a, 'm) optionT) sample"
where "sample_option p f = OptionT (sample p (\<lambda>x. run_option (f x)))"

lemma run_sample_option [simp]: "run_option (sample_option p f) = sample p (\<lambda>x. run_option (f x))"
by(simp add: sample_option_def)

lemma monad_prob_optionT [locale_witness]:
  assumes "monad_prob return bind sample"
  shows "monad_prob return_option bind_option sample_option"
proof -
  interpret monad_prob return bind sample by(fact assms)
  show ?thesis
  proof
    show "sample_option p (\<lambda>_. x) = x" for p x
      by(rule optionT.expand)(simp add: sample_const)
    show "sample_option (return_pmf x) f = f x" for f x
      by(rule optionT.expand)(simp add: sample_return_pmf)
    show "sample_option (bind_pmf p f) g = sample_option p (\<lambda>x. sample_option (f x) g)" for p f g
      by(rule optionT.expand)(simp add: sample_bind_pmf)
    show "sample_option p (\<lambda>x. sample_option q (f x)) = sample_option q (\<lambda>y. sample_option p (\<lambda>x. f x y))" for p q f
      by(rule optionT.expand)(auto intro!: sample_commute)
    show "bind_option (sample_option p f) g = sample_option p (\<lambda>x. bind_option (f x) g)" for p f g
      by(rule optionT.expand)(auto simp add: bind_sample1 run_bind_option)
    show "bind_option m (\<lambda>y. sample_option p (f y)) = sample_option p (\<lambda>x. bind_option m (\<lambda>y. f y x))" for m p f
      by(rule optionT.expand)(auto simp add: bind_sample2[symmetric] run_bind_option sample_const del: ext intro!: arg_cong2[where f=bind] ext split: option.split)
    show "sample_option p f = sample_option p g" if "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x" for p f g
      by(rule optionT.expand)(auto intro!: sample_cong dest: that)
  qed
qed

lemma monad_state_prob_optionT [locale_witness]:
  fixes get put
  assumes "monad_state_prob return bind get put sample"
  shows "monad_state_prob return_option bind_option (get_option get) (put_option put) sample_option"
proof -
  interpret monad_state_prob return bind get put sample by fact
  show ?thesis
  proof
    show "sample_option p (\<lambda>x. get_option get (f x)) = get_option get (\<lambda>s. sample_option p (\<lambda>x. f x s))" for p f
      by(rule optionT.expand)(simp add: sample_get)
  qed
qed

end

subsubsection \<open>Writer\<close>

context
  fixes tell :: "('w, 'm) tell"
begin

definition tell_option :: "('w, ('a, 'm) optionT) tell" 
where "tell_option w m = OptionT (tell w (run_option m))"

lemma run_tell_option [simp]: "run_option (tell_option w m) = tell w (run_option m)"
by(simp add: tell_option_def)

lemma monad_writer_optionT [locale_witness]:
  assumes "monad_writer return bind tell"
  shows "monad_writer return_option bind_option tell_option"
proof -
  interpret monad_writer return bind tell by fact
  show ?thesis
  proof
    show "bind_option (tell_option w m) f = tell_option w (bind_option m f)" for w m f
      by(rule optionT.expand)(simp add: run_bind_option bind_tell)
  qed
qed

end

subsubsection \<open>Non-determinism\<close>

context
  fixes alt :: "'m alt"
begin

definition alt_option :: "('a, 'm) optionT alt"
where "alt_option m1 m2 = OptionT (alt (run_option m1) (run_option m2))"

lemma run_alt_option [simp]: "run_option (alt_option m1 m2) = alt (run_option m1) (run_option m2)"
by(simp add: alt_option_def)

lemma monad_alt_optionT [locale_witness]:
  assumes "monad_alt return bind alt"
  shows "monad_alt return_option bind_option alt_option"
proof -
  interpret monad_alt return bind alt by fact
  show ?thesis
  proof
    show "alt_option (alt_option m1 m2) m3 = alt_option m1 (alt_option m2 m3)" for m1 m2 m3
      by(rule optionT.expand)(simp add: alt_assoc)
    show "bind_option (alt_option m m') f = alt_option (bind_option m f) (bind_option m' f)" for m m' f
      by(rule optionT.expand)(simp add: bind_alt1 run_bind_option)
  qed
qed

text \<open>
  The @{term fail} of @{typ "(_, _) optionT"} does not combine with @{term "alt"} of the inner monad
  because @{typ "(_, _) optionT"} injects failures with @{term "return None"} into the inner monad.
\<close>

end

subsubsection \<open>Resumption\<close>

context
  fixes pause :: "('o, 'i, 'm) pause"
begin

definition pause_option :: "('o, 'i, ('a, 'm) optionT) pause"
where "pause_option out c = OptionT (pause out (\<lambda>i. run_option (c i)))"

lemma run_pause_option [simp]: "run_option (pause_option out c) = pause out (\<lambda>i. run_option (c i))"
by(simp add: pause_option_def)

lemma monad_resumption_optionT [locale_witness]:
  assumes "monad_resumption return bind pause"
  shows "monad_resumption return_option bind_option pause_option"
proof -
  interpret monad_resumption return bind pause by fact
  show ?thesis
  proof
    show "bind_option (pause_option out c) f = pause_option out (\<lambda>i. bind_option (c i) f)" for out c f
      by(rule optionT.expand)(simp add: bind_pause run_bind_option)
  qed
qed

end

subsubsection \<open>Commutativity\<close>

lemma monad_commute_optionT [locale_witness]:
  assumes "monad_commute return bind"
  and "monad_discard return bind"
  shows "monad_commute return_option bind_option"
proof -
  interpret monad_commute return bind by fact
  interpret monad_discard return bind by fact
  show ?thesis
  proof
    fix m m' f
    have "run_option (bind_option m (\<lambda>x. bind_option m' (f x))) = 
      bind (run_option m) (\<lambda>x. bind (run_option m') (\<lambda>y. case (x, y) of (Some x', Some y') \<Rightarrow> run_option (f x' y') | _ \<Rightarrow> return None))"
      by(auto simp add: run_bind_option bind_const cong del: option.case_cong del: ext intro!: arg_cong2[where f=bind] ext split: option.split)
    also have "\<dots> = bind (run_option m') (\<lambda>y. bind (run_option m) (\<lambda>x. case (x, y) of (Some x', Some y') \<Rightarrow> run_option (f x' y') | _ \<Rightarrow> return None))"
      by(rule bind_commute)
    also have "\<dots> = run_option (bind_option m' (\<lambda>y. bind_option m (\<lambda>x. f x y)))"
      by(auto simp add: run_bind_option bind_const case_option_collapse cong del: option.case_cong del: ext intro!: arg_cong2[where f=bind] ext split: option.split)
    finally show "bind_option m (\<lambda>x. bind_option m' (f x)) = bind_option m' (\<lambda>y. bind_option m (\<lambda>x. f x y))"
      by(rule optionT.expand)
  qed
qed

end

subsubsection \<open>Parametricity\<close>

context includes lifting_syntax begin

lemma return_option_parametric [transfer_rule]:
  "((rel_option A ===> M) ===> A ===> rel_optionT M) return_option return_option"
unfolding return_option_def by transfer_prover

lemma bind_option_parametric [transfer_rule]:
  "((rel_option A ===> M) ===> (M ===> (rel_option A ===> M) ===> M)
   ===> rel_optionT M ===> (A ===> rel_optionT M) ===> rel_optionT M)
   bind_option bind_option"
unfolding bind_option_def by transfer_prover

lemma fail_option_parametric [transfer_rule]:
  "((rel_option A ===> M) ===> rel_optionT M) fail_option fail_option"
unfolding fail_option_def by transfer_prover

lemma ask_option_parametric [transfer_rule]:
  "(((R ===> M) ===> M) ===> (R ===> rel_optionT M) ===> rel_optionT M) ask_option ask_option"
unfolding ask_option_def by transfer_prover

lemma get_option_parametric [transfer_rule]:
  "(((S ===> M) ===> M) ===> (S ===> rel_optionT M) ===> rel_optionT M) get_option get_option"
unfolding get_option_def by transfer_prover

lemma put_option_parametric [transfer_rule]:
  "((S ===> M ===> M) ===> S ===> rel_optionT M ===> rel_optionT M) put_option put_option"
unfolding put_option_def by transfer_prover

lemma sample_option_parametric [transfer_rule]:
  "((rel_pmf P ===> (P ===> M) ===> M) ===> rel_pmf P ===> (P ===> rel_optionT M) ===> rel_optionT M)
   sample_option sample_option"
unfolding sample_option_def by transfer_prover

lemma alt_option_parametric [transfer_rule]:
  "((M ===> M ===> M) ===> rel_optionT M ===> rel_optionT M ===> rel_optionT M) alt_option alt_option"
unfolding alt_option_def by transfer_prover

lemma tell_option_parametric [transfer_rule]:
  "((W ===> M ===> M) ===> W ===> rel_optionT M ===> rel_optionT M) tell_option tell_option"
unfolding tell_option_def by transfer_prover

lemma pause_option_parametric [transfer_rule]:
  "((Out ===> (In ===> M) ===> M) ===> Out ===> (In ===> rel_optionT M) ===> rel_optionT M)
   pause_option pause_option"
unfolding pause_option_def by transfer_prover

end

subsection \<open>Reader monad transformer\<close>

datatype ('r, 'm) envT = EnvT (run_env: "'r \<Rightarrow> 'm")

context includes lifting_syntax begin 

definition rel_envT :: "('r \<Rightarrow> 'r' \<Rightarrow> bool) \<Rightarrow> ('m \<Rightarrow> 'm' \<Rightarrow> bool) \<Rightarrow> ('r, 'm) envT \<Rightarrow> ('r', 'm') envT \<Rightarrow> bool"
where "rel_envT R M = BNF_Def.vimage2p run_env run_env (R ===> M)"

lemma rel_envTI [intro!]: "(R ===> M) f g \<Longrightarrow> rel_envT R M (EnvT f) (EnvT g)"
by(simp add: rel_envT_def BNF_Def.vimage2p_def)

lemma rel_envT_simps: "rel_envT R M (EnvT f) (EnvT g) \<longleftrightarrow> (R ===> M) f g"
by(simp add: rel_envT_def BNF_Def.vimage2p_def)

lemma rel_envTE [cases pred]:
  assumes "rel_envT R M m m'"
  obtains f g where "m = EnvT f" "m' = EnvT g" "(R ===> M) f g"
using assms by(cases m; cases m'; auto  simp add: rel_envT_simps)

lemma rel_envT_eq [relator_eq]: "rel_envT (=) (=) = (=)"
by(auto simp add: rel_envT_def rel_fun_eq BNF_Def.vimage2p_def fun_eq_iff intro: envT.expand)

lemma rel_envT_mono [relator_mono]: "\<lbrakk> R \<le> R'; M \<le> M' \<rbrakk> \<Longrightarrow> rel_envT R' M \<le> rel_envT R M'"
by(simp add: rel_envT_def predicate2I vimage2p_mono fun_mono)

lemma EnvT_parametric [transfer_rule]: "((R ===> M) ===> rel_envT R M) EnvT EnvT"
by(simp add: rel_funI rel_envT_simps)

lemma run_env_parametric [transfer_rule]: "(rel_envT R M ===> R ===> M) run_env run_env"
by(auto elim!: rel_envTE)

lemma rec_envT_parametric [transfer_rule]:
  "(((R ===> M) ===> X) ===> rel_envT R M ===> X) rec_envT rec_envT"
by(auto 4 4 elim!: rel_envTE dest: rel_funD)

lemma case_envT_parametric [transfer_rule]:
  "(((R ===> M) ===> X) ===> rel_envT R M ===> X) case_envT case_envT"
by(auto 4 4 elim!: rel_envTE dest: rel_funD)

end

subsubsection \<open>Plain monad and ask\<close>

context
  fixes return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
begin

definition return_env :: "('a, ('r, 'm) envT) return"
where "return_env x = EnvT (\<lambda>_. return x)"

primrec bind_env :: "('a, ('r, 'm) envT) bind"
where "bind_env (EnvT x) f = EnvT (\<lambda>r. bind (x r) (\<lambda>y. run_env (f y) r))"

definition ask_env :: "('r, ('r, 'm) envT) ask"
where "ask_env f = EnvT (\<lambda>r. run_env (f r) r)"

lemma run_bind_env [simp]: "run_env (bind_env x f) r = bind (run_env x r) (\<lambda>y. run_env (f y) r)"
by(cases x) simp

lemma run_return_env [simp]: "run_env (return_env x) r = return x"
by(simp add: return_env_def)

lemma run_ask_env [simp]: "run_env (ask_env f) r = run_env (f r) r"
by(simp add: ask_env_def)

context
  assumes monad: "monad return bind"
begin

interpretation monad return "bind :: ('a, 'm) bind" by(fact monad)

lemma monad_envT [locale_witness]: "monad return_env bind_env"
proof
  show "bind_env (bind_env x f) g = bind_env x (\<lambda>x. bind_env (f x) g)" 
    for x :: "('r, 'm) envT" and f :: "'a \<Rightarrow> ('r, 'm) envT" and g :: "'a \<Rightarrow> ('r, 'm) envT"
    by(rule envT.expand)(auto simp add: bind_assoc return_bind)
  show "bind_env (return_env x) f = f x" for f :: "'a \<Rightarrow> ('r, 'm) envT" and x
    by(rule envT.expand)(simp add: return_bind return_env_def)
  show "bind_env x (return_env :: ('a, ('r, 'm) envT) return) = x" for x :: "('r, 'm) envT"
    by(rule envT.expand)(simp add: bind_return fun_eq_iff)
qed

lemma monad_reader_envT [locale_witness]:
  "monad_reader return_env bind_env ask_env"
proof
  show "ask_env (\<lambda>r. ask_env (f r)) = ask_env (\<lambda>r. f r r)" for f :: "'r \<Rightarrow> 'r \<Rightarrow> ('r, 'm) envT"
    by(rule envT.expand)(auto simp add: fun_eq_iff)
  show "ask_env (\<lambda>_. x) = x" for x :: "('r, 'm) envT"
    by(rule envT.expand)(auto simp add: fun_eq_iff)
  show "bind_env (ask_env f) g = ask_env (\<lambda>r. bind_env (f r) g)" for f :: "'r \<Rightarrow> ('r, 'm) envT" and g
    by(rule envT.expand)(auto simp add: fun_eq_iff)
  show "bind_env m (\<lambda>x. ask_env (f x)) = ask_env (\<lambda>r. bind_env m (\<lambda>x. f x r))" for m :: "('r, 'm) envT" and f
    by(rule envT.expand)(auto simp add: fun_eq_iff)
qed

end

subsubsection \<open>Failure\<close>

context
  fixes fail :: "'m fail"
begin

definition fail_env :: "('r, 'm) envT fail"
where "fail_env = EnvT (\<lambda>r. fail)"

lemma run_fail_env [simp]: "run_env fail_env r = fail"
by(simp add: fail_env_def)

lemma monad_fail_envT [locale_witness]:
  assumes "monad_fail return bind fail"
  shows "monad_fail return_env bind_env fail_env"
proof -
  interpret monad_fail return bind fail by(fact assms)
  have "bind_env fail_env f = fail_env" for f :: "'a \<Rightarrow> ('r, 'm) envT"
    by(rule envT.expand)(simp add: fun_eq_iff fail_bind)
  then show ?thesis by unfold_locales
qed

context
  fixes catch :: "'m catch"
begin

definition catch_env :: "('r, 'm) envT catch"
where "catch_env m1 m2 = EnvT (\<lambda>r. catch (run_env m1 r) (run_env m2 r))"

lemma run_catch_env [simp]: "run_env (catch_env m1 m2) r = catch (run_env m1 r) (run_env m2 r)"
by(simp add: catch_env_def)

lemma monad_catch_envT [locale_witness]:
  assumes "monad_catch return bind fail catch"
  shows "monad_catch return_env bind_env fail_env catch_env"
proof -
  interpret monad_catch return bind fail catch by fact
  show ?thesis
  proof
    show "catch_env (return_env x) m = return_env x" for x and m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff catch_return)
    show "catch_env fail_env m = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff catch_fail)
    show "catch_env m fail_env = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff catch_fail2)
    show "catch_env (catch_env m m') m'' = catch_env m (catch_env m' m'')"
      for m m' m'' :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff catch_assoc)
  qed
qed
       
end

end

subsubsection \<open>State\<close>

context
  fixes get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
begin

definition get_env :: "('s, ('r, 'm) envT) get"
where "get_env f = EnvT (\<lambda>r. get (\<lambda>s. run_env (f s) r))"

definition put_env :: "('s, ('r, 'm) envT) put"
where "put_env s m = EnvT (\<lambda>r. put s (run_env m r))"

lemma run_get_env [simp]: "run_env (get_env f) r = get (\<lambda>s. run_env (f s) r)"
by(simp add: get_env_def)

lemma run_put_env [simp]: "run_env (put_env s m) r = put s (run_env m r)"
by(simp add: put_env_def)

lemma monad_state_envT [locale_witness]:
  assumes "monad_state return bind get put"
  shows "monad_state return_env bind_env get_env put_env"
proof -
  interpret monad_state return bind get put by(fact assms)
  show ?thesis
  proof
    show "put_env s (get_env f) = put_env s (f s)" for s :: 's and f :: "'s \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff put_get)
    show "get_env (\<lambda>s. get_env (f s)) = get_env (\<lambda>s. f s s)" for f :: "'s \<Rightarrow> 's \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff get_get)
    show "put_env s (put_env s' m) = put_env s' m" for s s' :: 's and m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff put_put)
    show "get_env (\<lambda>s. put_env s m) = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff get_put)
    show "get_env (\<lambda>_. m) = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff get_const)
    show "bind_env (get_env f) g = get_env (\<lambda>s. bind_env (f s) g)" for f :: "'s \<Rightarrow> ('r, 'm) envT" and g
      by(rule envT.expand)(simp add: fun_eq_iff bind_get)
    show "bind_env (put_env s m) f = put_env s (bind_env m f)" for s and m :: "('r, 'm) envT" and f
      by(rule envT.expand)(simp add: fun_eq_iff bind_put)    
  qed
qed

subsubsection \<open>Probability\<close>

context
  fixes sample :: "('p, 'm) sample"
begin

definition sample_env :: "('p, ('r, 'm) envT) sample"
where "sample_env p f = EnvT (\<lambda>r. sample p (\<lambda>x. run_env (f x) r))"

lemma run_sample_env [simp]: "run_env (sample_env p f) r = sample p (\<lambda>x. run_env (f x) r)"
by(simp add: sample_env_def)

lemma monad_prob_envT [locale_witness]:
  assumes "monad_prob return bind sample"
  shows "monad_prob return_env bind_env sample_env"
proof -
  interpret monad_prob return bind sample by(fact assms)
  show ?thesis
  proof
    show "sample_env p (\<lambda>_. x) = x" for p :: "'p pmf" and x :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff sample_const)
    show "sample_env (return_pmf x) f = f x" for f :: "'p \<Rightarrow> ('r, 'm) envT" and x
      by(rule envT.expand)(simp add: fun_eq_iff sample_return_pmf)
    show "sample_env (bind_pmf p f) g = sample_env p (\<lambda>x. sample_env (f x) g)" for f and g :: "'p \<Rightarrow> ('r, 'm) envT" and p
      by(rule envT.expand)(simp add: fun_eq_iff sample_bind_pmf)
    show "sample_env p (\<lambda>x. sample_env q (f x)) = sample_env q (\<lambda>y. sample_env p (\<lambda>x. f x y))"
      for p q :: "'p pmf" and f :: "'p \<Rightarrow> 'p \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(auto simp add: fun_eq_iff intro: sample_commute)
    show "bind_env (sample_env p f) g = sample_env p (\<lambda>x. bind_env (f x) g)"
      for p and f :: "'p \<Rightarrow> ('r, 'm) envT" and g
      by(rule envT.expand)(simp add: fun_eq_iff bind_sample1)
    show "bind_env m (\<lambda>y. sample_env p (f y)) = sample_env p (\<lambda>x. bind_env m (\<lambda>y. f y x))"
      for m p and f :: "'a \<Rightarrow> 'p \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff bind_sample2)
    show "sample_env p f = sample_env p g" if "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x" for p and f g :: "'p \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(auto simp add: fun_eq_iff intro!: sample_cong dest: that)
  qed
qed

lemma monad_state_prob_envT [locale_witness]:
  assumes "monad_state_prob return bind get put sample"
  shows "monad_state_prob return_env bind_env get_env put_env sample_env"
proof -
  interpret monad_state_prob return bind get put sample by fact
  show ?thesis
  proof
    show "sample_env p (\<lambda>x. get_env (f x)) = get_env (\<lambda>s. sample_env p (\<lambda>x. f x s))"
      for p and f :: "'p \<Rightarrow> 's \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff sample_get)
  qed
qed

end

end

subsubsection \<open>Non-determinism\<close>

context
  fixes alt :: "'m alt"
begin

definition alt_env :: "('r, 'm) envT alt"
where "alt_env m1 m2 = EnvT (\<lambda>r. alt (run_env m1 r) (run_env m2 r))"

lemma run_alt_env [simp]: "run_env (alt_env m1 m2) r = alt (run_env m1 r) (run_env m2 r)"
by(simp add: alt_env_def)

lemma monad_alt_envT [locale_witness]:
  assumes "monad_alt return bind alt"
  shows "monad_alt return_env bind_env alt_env"
proof -
  interpret monad_alt return bind alt by fact
  show ?thesis
  proof
    show "alt_env (alt_env m1 m2) m3 = alt_env m1 (alt_env m2 m3)" for m1 m2 m3 :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff alt_assoc)
    show "bind_env (alt_env m m') f = alt_env (bind_env m f) (bind_env m' f)" for m m' :: "('r, 'm) envT" and f
      by(rule envT.expand)(simp add: fun_eq_iff bind_alt1)
  qed
qed

lemma monad_fail_alt_envT [locale_witness]:
  fixes fail
  assumes "monad_fail_alt return bind fail alt"
  shows "monad_fail_alt return_env bind_env (fail_env fail) alt_env"
proof -
  interpret monad_fail_alt return bind fail alt by fact
  show ?thesis
  proof
    show "alt_env (fail_env fail) m = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: alt_fail1 fun_eq_iff)
    show "alt_env m (fail_env fail) = m" for m :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: alt_fail2 fun_eq_iff)
  qed
qed

end

subsubsection \<open>Resumption\<close>

context
  fixes pause :: "('o, 'i, 'm) pause"
begin

definition pause_env :: "('o, 'i, ('r, 'm) envT) pause"
where "pause_env out c = EnvT (\<lambda>r. pause out (\<lambda>i. run_env (c i) r))"

lemma run_pause_env [simp]:
  "run_env (pause_env out c) r = pause out (\<lambda>i. run_env (c i) r)"
by(simp add: pause_env_def)

lemma monad_resumption_envT [locale_witness]:
  assumes "monad_resumption return bind pause"
  shows "monad_resumption return_env bind_env pause_env"
proof -
  interpret monad_resumption return bind pause by fact
  show ?thesis
  proof
    show "bind_env (pause_env out c) f = pause_env out (\<lambda>i. bind_env (c i) f)" for out f and c :: "'i \<Rightarrow> ('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff bind_pause)
  qed
qed

end

subsubsection \<open>Writer\<close>

context
  fixes tell :: "('w, 'm) tell"
begin

definition tell_env :: "('w, ('r, 'm) envT) tell"
where "tell_env w m = EnvT (\<lambda>r. tell w (run_env m r))"

lemma run_tell_env [simp]: "run_env (tell_env w m) r = tell w (run_env m r)"
by(simp add: tell_env_def)

lemma monad_writer_envT [locale_witness]:
  assumes "monad_writer return bind tell"
  shows "monad_writer return_env bind_env tell_env"
proof -
  interpret monad_writer return bind tell by fact
  show ?thesis
  proof
    show "bind_env (tell_env w m) f = tell_env w (bind_env m f)" for w and m :: "('r, 'm) envT" and f
      by(rule envT.expand)(simp add: bind_tell fun_eq_iff)
  qed
qed

end

subsubsection \<open>Commutativity\<close>

lemma monad_commute_envT [locale_witness]:
  assumes "monad_commute return bind"
  shows "monad_commute return_env bind_env"
proof -
  interpret monad_commute return bind by fact
  show ?thesis
  proof
    show "bind_env m (\<lambda>x. bind_env m' (f x)) = bind_env m' (\<lambda>y. bind_env m (\<lambda>x. f x y))"
      for f and m m' :: "('r, 'm) envT"
      by(rule envT.expand)(auto simp add: fun_eq_iff intro: bind_commute)
  qed
qed

subsubsection \<open>Discardability\<close>

lemma monad_discard_envT [locale_witness]:
  assumes "monad_discard return bind"
  shows "monad_discard return_env bind_env"
proof -
  interpret monad_discard return bind by fact
  show ?thesis
  proof
    show "bind_env m (\<lambda>_. m') = m'" for m m' :: "('r, 'm) envT"
      by(rule envT.expand)(simp add: fun_eq_iff bind_const)
  qed
qed

end

subsubsection \<open>Parametricity\<close>

context includes lifting_syntax begin

lemma return_env_parametric [transfer_rule]:
  "((A ===> M) ===> A ===> rel_envT R M) return_env return_env"
unfolding return_env_def by transfer_prover

lemma bind_env_parametric [transfer_rule]:
  "((M ===> (A ===> M) ===> M) ===> rel_envT R M ===> (A ===> rel_envT R M) ===> rel_envT R M)
   bind_env bind_env"
unfolding bind_env_def by transfer_prover

lemma ask_env_parametric [transfer_rule]: "((R ===> rel_envT R M) ===> rel_envT R M) ask_env ask_env"
unfolding ask_env_def by transfer_prover

lemma fail_env_parametric [transfer_rule]: "(M ===> rel_envT R M) fail_env fail_env"
unfolding fail_env_def by transfer_prover

lemma catch_env_parametric [transfer_rule]: 
  "((M ===> M ===> M) ===> rel_envT R M ===> rel_envT R M ===> rel_envT R M) catch_env catch_env"
unfolding catch_env_def by transfer_prover

lemma get_env_parametric [transfer_rule]:
  "(((S ===> M) ===> M) ===> (S ===> rel_envT R M) ===> rel_envT R M) get_env get_env"
unfolding get_env_def by transfer_prover

lemma put_env_parametric [transfer_rule]:
  "((S ===> M ===> M) ===> S ===> rel_envT R M ===> rel_envT R M) put_env put_env"
unfolding put_env_def by transfer_prover

lemma sample_env_parametric [transfer_rule]:
  "((rel_pmf P ===> (P ===> M) ===> M) ===> rel_pmf P ===> (P ===> rel_envT R M) ===> rel_envT R M)
  sample_env sample_env"
unfolding sample_env_def by transfer_prover

lemma alt_env_parametric [transfer_rule]:
  "((M ===> M ===> M) ===> rel_envT R M ===> rel_envT R M ===> rel_envT R M) alt_env alt_env"
unfolding alt_env_def by transfer_prover

lemma pause_env_parametric [transfer_rule]:
  "((Out ===> (In ===> M) ===> M) ===> Out ===> (In ===> rel_envT R M) ===> rel_envT R M)
   pause_env pause_env"
unfolding pause_env_def by transfer_prover

lemma tell_env_parametric [transfer_rule]:
  "((W ===> M ===> M) ===> W ===> rel_envT R M ===> rel_envT R M) tell_env tell_env"
unfolding tell_env_def by transfer_prover

end

subsection \<open>Writer monad transformer\<close>

text \<open>
  We implement a simple writer monad which collects all the output in a list. It would also have
  been possible to use a monoid instead. The phantom type variables @{typ 'a} and @{typ 'w} are needed to
  avoid hidden polymorphism when overloading the monad operations for the writer monad
  transformer.
\<close>

datatype ('w, 'a, 'm) writerT = WriterT (run_writer: 'm)

context
  fixes return :: "('a \<times> 'w list, 'm) return"
  and bind :: "('a \<times> 'w list, 'm) bind"
begin

definition return_writer :: "('a, ('w, 'a, 'm) writerT) return"
where "return_writer x = WriterT (return (x, []))"

definition bind_writer :: "('a, ('w, 'a, 'm) writerT) bind"
where "bind_writer m f = WriterT (bind (run_writer m) (\<lambda>(a, ws). bind (run_writer (f a)) (\<lambda>(b, ws'). return (b, ws @ ws'))))"

definition tell_writer :: "('w, ('w, 'a, 'm) writerT) tell"
where "tell_writer w m = WriterT (bind (run_writer m) (\<lambda>(a, ws). return (a, w # ws)))"

lemma run_return_writer [simp]: "run_writer (return_writer x) = return (x, [])"
by(simp add: return_writer_def)

lemma run_bind_writer [simp]:
  "run_writer (bind_writer m f) = bind (run_writer m) (\<lambda>(a, ws). bind (run_writer (f a)) (\<lambda>(b, ws'). return (b, ws @ ws')))"
by(simp add: bind_writer_def)

lemma run_tell_writer [simp]:
  "run_writer (tell_writer w m) = bind (run_writer m) (\<lambda>(a, ws). return (a, w # ws))"
by(simp add: tell_writer_def)

context
  assumes "monad return bind"
begin

interpretation monad return bind by fact

lemma monad_writerT [locale_witness]: "monad return_writer bind_writer"
proof
  show "bind_writer (bind_writer x f) g = bind_writer x (\<lambda>y. bind_writer (f y) g)" for x f g
    by(rule writerT.expand)(simp add: bind_assoc split_def return_bind)
  show "bind_writer (return_writer x) f = f x" for  x f
    by(rule writerT.expand)(simp add: bind_return return_bind)
  show "bind_writer x return_writer = x" for x
    by(rule writerT.expand)(simp add: bind_return return_bind)
qed

lemma monad_writer_writerT [locale_witness]: "monad_writer return_writer bind_writer tell_writer"
proof
  show "bind_writer (tell_writer w m) f = tell_writer w (bind_writer m f)" for w m f
    by(rule writerT.expand)(simp add: bind_assoc split_def return_bind)
qed

end

subsubsection \<open>Failure\<close>

context
  fixes fail :: "'m fail"
begin

definition fail_writer :: "('w, 'a, 'm) writerT fail"
where "fail_writer = WriterT fail"

lemma run_fail_writer [simp]: "run_writer fail_writer = fail"
by(simp add: fail_writer_def)

lemma monad_fail_writerT [locale_witness]:
  assumes "monad_fail return bind fail"
  shows "monad_fail return_writer bind_writer fail_writer"
proof -
  interpret monad_fail return bind fail by fact
  show ?thesis
  proof
    show "bind_writer fail_writer f = fail_writer" for f
      by(rule writerT.expand)(simp add: fail_bind)
  qed
qed

text \<open>
  Just like for the state monad, we cannot lift @{term catch} because the output before the failure would be lost.
\<close>

subsubsection \<open>State\<close>

context
  fixes get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
begin

definition get_writer :: "('s, ('w, 'a, 'm) writerT) get"
where "get_writer f = WriterT (get (\<lambda>s. run_writer (f s)))"

definition put_writer :: "('s, ('w, 'a, 'm) writerT) put"
where "put_writer s m = WriterT (put s (run_writer m))"

lemma run_get_writer [simp]: "run_writer (get_writer f) = get (\<lambda>s. run_writer (f s))"
by(simp add: get_writer_def)

lemma run_put_writer [simp]: "run_writer (put_writer s m) = put s (run_writer m)"
by(simp add: put_writer_def)

lemma monad_state_writerT [locale_witness]:
  assumes "monad_state return bind get put"
  shows "monad_state return_writer bind_writer get_writer put_writer"
proof -
  interpret monad_state return bind get put by fact
  show ?thesis
  proof
    show "put_writer s (get_writer f) = put_writer s (f s)" for s f
      by(rule writerT.expand)(simp add: put_get)
    show "get_writer (\<lambda>s. get_writer (f s)) = get_writer (\<lambda>s. f s s)" for f
      by(rule writerT.expand)(simp add: get_get)
    show "put_writer s (put_writer s' m) = put_writer s' m" for s s' m
      by(rule writerT.expand)(simp add: put_put)
    show "get_writer (\<lambda>s. put_writer s m) = m" for m
      by(rule writerT.expand)(simp add: get_put)
    show "get_writer (\<lambda>_. m) = m" for m
      by(rule writerT.expand)(simp add: get_const)
    show "bind_writer (get_writer f) g = get_writer (\<lambda>s. bind_writer (f s) g)" for f g
      by(rule writerT.expand)(simp add: bind_get)
    show "bind_writer (put_writer s m) f = put_writer s (bind_writer m f)" for s m f
      by(rule writerT.expand)(simp add: bind_put)
  qed
qed

subsubsection  \<open>Probability\<close>

context
  fixes sample :: "('p, 'm) sample"
begin

definition sample_writer :: "('p, ('w, 'a, 'm) writerT) sample"
where "sample_writer p f = WriterT (sample p (\<lambda>p. run_writer (f p)))"

lemma run_sample_writer [simp]: "run_writer (sample_writer p f) = sample p (\<lambda>p. run_writer (f p))"
by(simp add: sample_writer_def)

lemma monad_prob_writerT [locale_witness]:
  assumes "monad_prob return bind sample"
  shows "monad_prob return_writer bind_writer sample_writer"
proof -
  interpret monad_prob return bind sample by fact
  show ?thesis
  proof
    show "sample_writer p (\<lambda>_. m) = m" for p m
      by(rule writerT.expand)(simp add: sample_const)
    show "sample_writer (return_pmf x) f = f x" for x f
      by(rule writerT.expand)(simp add: sample_return_pmf)
    show "sample_writer (p \<bind> f) g = sample_writer p (\<lambda>x. sample_writer (f x) g)" for p f g
      by(rule writerT.expand)(simp add: sample_bind_pmf)
    show "sample_writer p (\<lambda>x. sample_writer q (f x)) = sample_writer q (\<lambda>y. sample_writer p (\<lambda>x. f x y))"
      for p q f by(rule writerT.expand)(auto intro: sample_commute)
    show "bind_writer (sample_writer p f) g = sample_writer p (\<lambda>x. bind_writer (f x) g)" for p f g
      by(rule writerT.expand)(simp add: bind_sample1)
    show "bind_writer m (\<lambda>y. sample_writer p (f y)) = sample_writer p (\<lambda>x. bind_writer m (\<lambda>y. f y x))"
      for m p f by(rule writerT.expand)(simp add: bind_sample2[symmetric] bind_sample1 split_def)
    show "(\<And>x. x \<in> set_pmf p \<Longrightarrow> f x = g x) \<Longrightarrow> sample_writer p f = sample_writer p g" for p f g
      by(rule writerT.expand)(simp cong: sample_cong)
  qed
qed

lemma monad_state_prob_writerT [locale_witness]:
  assumes "monad_state_prob return bind get put sample"
  shows "monad_state_prob return_writer bind_writer get_writer put_writer sample_writer"
proof -
  interpret monad_state_prob return bind get put sample by fact
  show ?thesis
  proof
    show "sample_writer p (\<lambda>x. get_writer (f x)) = get_writer (\<lambda>s. sample_writer p (\<lambda>x. f x s))" for p f
      by(rule writerT.expand)(simp add: sample_get)
  qed
qed

end

subsubsection \<open>Reader\<close>

context
  fixes ask :: "('r, 'm) ask"
begin

definition ask_writer :: "('r, ('w, 'a, 'm) writerT) ask"
where "ask_writer f = WriterT (ask (\<lambda>r. run_writer (f r)))"

lemma run_ask_writer [simp]: "run_writer (ask_writer f) = ask (\<lambda>r. run_writer (f r))"
by(simp add: ask_writer_def)

lemma monad_reader_writerT [locale_witness]:
  assumes "monad_reader return bind ask"
  shows "monad_reader return_writer bind_writer ask_writer"
proof -
  interpret monad_reader return bind ask by fact
  show ?thesis
  proof
    show "ask_writer (\<lambda>r. ask_writer (f r)) = ask_writer (\<lambda>r. f r r)" for f
      by(rule writerT.expand)(simp add: ask_ask)
    show "ask_writer (\<lambda>_. m) = m" for m
      by(rule writerT.expand)(simp add: ask_const)
    show "bind_writer (ask_writer f) g = ask_writer (\<lambda>r. bind_writer (f r) g)" for f g
      by(rule writerT.expand)(simp add: bind_ask)
    show "bind_writer m (\<lambda>x. ask_writer (f x)) = ask_writer (\<lambda>r. bind_writer m (\<lambda>x. f x r))"
      for m f by(rule writerT.expand)(simp add: split_def bind_ask2[symmetric] bind_ask)
  qed
qed

lemma monad_reader_state_writerT [locale_witness]:
  assumes "monad_reader_state return bind ask get put"
  shows "monad_reader_state return_writer bind_writer ask_writer get_writer put_writer"
proof -
  interpret monad_reader_state return bind ask get put by fact
  show ?thesis
  proof
    show "ask_writer (\<lambda>r. get_writer (f r)) = get_writer (\<lambda>s. ask_writer (\<lambda>r. f r s))"
      for f by(rule writerT.expand)(simp add: ask_get)
    show "put_writer s (ask_writer f) = ask_writer (\<lambda>r. put_writer s (f r))" for s f
      by(rule writerT.expand)(simp add: put_ask)
  qed
qed

end

end

subsubsection \<open>Resumption\<close>

context
  fixes pause :: "('o, 'i, 'm) pause"
begin

definition pause_writer :: "('o, 'i, ('w, 'a, 'm) writerT) pause"
where "pause_writer out c = WriterT (pause out (\<lambda>input. run_writer (c input)))"

lemma run_pause_writer [simp]:
  "run_writer (pause_writer out c) = pause out (\<lambda>input. run_writer (c input))"
by(simp add: pause_writer_def)

lemma monad_resumption_writerT [locale_witness]:
  assumes "monad_resumption return bind pause"
  shows "monad_resumption return_writer bind_writer pause_writer"
proof -
  interpret monad_resumption return bind pause by fact
  show ?thesis
  proof
    show "bind_writer (pause_writer out c) f = pause_writer out (\<lambda>i. bind_writer (c i) f)" for out c f
      by(rule writerT.expand)(simp add: bind_pause)
  qed
qed

end

subsubsection \<open>Non-determinism\<close>

context
  fixes alt :: "'m alt"
begin

definition alt_writer :: "('w, 'a, 'm) writerT alt"
where "alt_writer m m' = WriterT (alt (run_writer m) (run_writer m'))"

lemma run_alt_writer [simp]: "run_writer (alt_writer m m') = alt (run_writer m) (run_writer m')"
by(simp add: alt_writer_def)

lemma monad_alt_writerT [locale_witness]:
  assumes "monad_alt return bind alt"
  shows "monad_alt return_writer bind_writer alt_writer"
proof -
  interpret monad_alt return bind alt by fact
  show ?thesis
  proof
    show "alt_writer (alt_writer m1 m2) m3 = alt_writer m1 (alt_writer m2 m3)" 
      for m1 m2 m3 by(rule writerT.expand)(simp add: alt_assoc)
    show "bind_writer (alt_writer m m') f = alt_writer (bind_writer m f) (bind_writer m' f)"
      for m m' f by(rule writerT.expand)(simp add: bind_alt1)
  qed
qed

lemma monad_fail_alt_writerT [locale_witness]:
  assumes "monad_fail_alt return bind fail alt"
  shows "monad_fail_alt return_writer bind_writer fail_writer alt_writer"
proof -
  interpret monad_fail_alt return bind fail alt by fact
  show ?thesis
  proof
    show "alt_writer fail_writer m = m" for m
      by(rule writerT.expand)(simp add: alt_fail1)
    show "alt_writer m fail_writer = m" for m
      by(rule writerT.expand)(simp add: alt_fail2)
  qed
qed

end

end

end

subsubsection \<open>Parametricity\<close>

context includes lifting_syntax begin

lemma return_writer_parametric [transfer_rule]:
  "((rel_prod A (list_all2 W) ===> M) ===> A ===> rel_writerT W A M) return_writer return_writer"
unfolding return_writer_def by transfer_prover

lemma bind_writer_parametric [transfer_rule]:
  "((rel_prod A (list_all2 W) ===> M) ===> (M ===> (rel_prod A (list_all2 W) ===> M) ===> M)
   ===> rel_writerT W A M ===> (A ===> rel_writerT W A M) ===> rel_writerT W A M)
   bind_writer bind_writer"
unfolding bind_writer_def by transfer_prover

lemma tell_writer_parametric [transfer_rule]:
  "((rel_prod A (list_all2 W) ===> M) ===> (M ===> (rel_prod A (list_all2 W) ===> M) ===> M)
   ===> W ===> rel_writerT W A M ===> rel_writerT W A M)
   tell_writer tell_writer"
unfolding tell_writer_def by transfer_prover

lemma ask_writer_parametric [transfer_rule]: 
  "(((R ===> M) ===> M) ===> (R ===> rel_writerT W A M) ===> rel_writerT W A M) ask_writer ask_writer"
unfolding ask_writer_def by transfer_prover

lemma fail_writer_parametric [transfer_rule]:
  "(M ===> rel_writerT W A M) fail_writer fail_writer"
unfolding fail_writer_def by transfer_prover

lemma get_writer_parametric [transfer_rule]:
  "(((S ===> M) ===> M) ===> (S ===> rel_writerT W A M) ===> rel_writerT W A M) get_writer get_writer"
unfolding get_writer_def by transfer_prover

lemma put_writer_parametric [transfer_rule]:
  "((S ===> M ===> M) ===> S ===> rel_writerT W A M ===> rel_writerT W A M) put_writer put_writer"
unfolding put_writer_def by transfer_prover

lemma sample_writer_parametric [transfer_rule]:
  "((rel_pmf P ===> (P ===> M) ===> M) ===> rel_pmf P ===> (P ===> rel_writerT W A M) ===> rel_writerT W A M)
  sample_writer sample_writer"
unfolding sample_writer_def by transfer_prover

lemma alt_writer_parametric [transfer_rule]:
  "((M ===> M ===> M) ===> rel_writerT W A M ===> rel_writerT W A M ===> rel_writerT W A M)
   alt_writer alt_writer"
unfolding alt_writer_def by transfer_prover

lemma pause_writer_parametric [transfer_rule]:
  "((Out ===> (In ===> M) ===> M) ===> Out ===> (In ===> rel_writerT W A M) ===> rel_writerT W A M)
   pause_writer pause_writer"
unfolding pause_writer_def by transfer_prover

end

subsection \<open>Continuation monad transformer\<close>

datatype ('a, 'm) contT = ContT (run_cont: "('a \<Rightarrow> 'm) \<Rightarrow> 'm")

subsubsection \<open>CallCC\<close>

type_synonym ('a, 'm) callcc = "(('a \<Rightarrow> 'm) \<Rightarrow> 'm) \<Rightarrow> 'm"

definition callcc_cont :: "('a, ('a, 'm) contT) callcc"
where "callcc_cont f = ContT (\<lambda>k. run_cont (f (\<lambda>x. ContT (\<lambda>_. k x))) k)"

lemma run_callcc_cont [simp]: "run_cont (callcc_cont f) k = run_cont (f (\<lambda>x. ContT (\<lambda>_. k x))) k"
by(simp add: callcc_cont_def)

subsubsection \<open>Plain monad\<close>

definition return_cont :: "('a, ('a, 'm) contT) return"
where "return_cont x = ContT (\<lambda>k. k x)"

definition bind_cont :: "('a, ('a, 'm) contT) bind"
where "bind_cont m f = ContT (\<lambda>k. run_cont m (\<lambda>x. run_cont (f x) k))"

lemma run_return_cont [simp]: "run_cont (return_cont x) k = k x"
by(simp add: return_cont_def)

lemma run_bind_cont [simp]: "run_cont (bind_cont m f) k = run_cont m (\<lambda>x. run_cont (f x) k)"
by(simp add: bind_cont_def)

lemma monad_contT [locale_witness]: "monad return_cont bind_cont" (is "monad ?return ?bind")
proof
  show "?bind (?bind x f) g = ?bind x (\<lambda>x. ?bind (f x) g)" for x f g
    by(rule contT.expand)(simp add: fun_eq_iff)
  show "?bind (?return x) f = f x" for f x
    by(rule contT.expand)(simp add: fun_eq_iff)
  show "?bind x ?return = x" for x
    by(rule contT.expand)(simp add: fun_eq_iff)
qed

subsubsection \<open>Failure\<close>

context
  fixes fail :: "'m fail"
begin

definition fail_cont :: "('a, 'm) contT fail"
where "fail_cont = ContT (\<lambda>_. fail)"

lemma run_fail_cont [simp]: "run_cont fail_cont k = fail"
by(simp add: fail_cont_def)

lemma monad_fail_contT [locale_witness]: "monad_fail return_cont bind_cont fail_cont"
proof
  show "bind_cont fail_cont f = fail_cont" for f :: "'a \<Rightarrow> ('a, 'm) contT"
    by(rule contT.expand)(simp add: fun_eq_iff)
qed

end

subsubsection \<open>State\<close>

context
  fixes get :: "('s, 'm) get"
  and put :: "('s, 'm) put"
begin

definition get_cont :: "('s, ('a, 'm) contT) get"
where "get_cont f = ContT (\<lambda>k. get (\<lambda>s. run_cont (f s) k))"

definition put_cont :: "('s, ('a, 'm) contT) put"
where "put_cont s m = ContT (\<lambda>k. put s (run_cont m k))"

lemma run_get_cont [simp]: "run_cont (get_cont f) k = get (\<lambda>s. run_cont (f s) k)"
by(simp add: get_cont_def)

lemma run_put_cont [simp]: "run_cont (put_cont s m) k = put s (run_cont m k)"
by(simp add: put_cont_def)

lemma monad_state_contT [locale_witness]:
  assumes "monad_state return' bind' get put" \<comment> \<open>We don't need the plain monad operations for lifting.\<close>
  shows "monad_state return_cont bind_cont get_cont (put_cont :: ('s, ('a, 'm) contT) put)"
  (is "monad_state ?return ?bind ?get ?put")
proof -
  interpret monad_state return' bind' get put by(fact assms)
  show ?thesis
  proof
    show "put_cont s (get_cont f) = put_cont s (f s)" for s :: 's and f :: "'s \<Rightarrow> ('a, 'm) contT"
      by(rule contT.expand)(simp add: put_get fun_eq_iff)
    show "get_cont (\<lambda>s. get_cont (f s)) = get_cont (\<lambda>s. f s s)" for f :: "'s \<Rightarrow> 's \<Rightarrow> ('a, 'm) contT"
      by(rule contT.expand)(simp add: get_get fun_eq_iff)
    show "put_cont s (put_cont s' m) = put_cont s' m" for s s' and m :: "('a, 'm) contT"
      by(rule contT.expand)(simp add: put_put fun_eq_iff)
    show "get_cont (\<lambda>s. put_cont s m) = m" for m :: "('a, 'm) contT"
      by(rule contT.expand)(simp add: get_put fun_eq_iff)
    show "get_cont (\<lambda>_. m) = m" for m :: "('a, 'm) contT"
      by(rule contT.expand)(simp add: get_const fun_eq_iff)
    show "bind_cont (get_cont f) g = get_cont (\<lambda>s. bind_cont (f s) g)"
      for f :: "'s \<Rightarrow> ('a, 'm) contT" and g 
      by(rule contT.expand)(simp add: fun_eq_iff)
    show "bind_cont (put_cont s m) f = put_cont s (bind_cont m f)" for s and m :: "('a, 'm) contT" and f
      by(rule contT.expand)(simp add: fun_eq_iff)
  qed
qed

end


section \<open>Correspondence relations between monads\<close>

context includes lifting_syntax begin

subsection \<open>Identity and Probability\<close>

named_theorems cr_id_prob_transfer

inductive cr_id_prob :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a id \<Rightarrow> 'b prob \<Rightarrow> bool" for A
where "A x y \<Longrightarrow> cr_id_prob A (return_id x) (return_pmf y)"

inductive_simps cr_id_prob_simps [simp]: "cr_id_prob A (return_id x) (return_pmf y)"

lemma cr_id_prob_return [cr_id_prob_transfer]: "(A ===> cr_id_prob A) return_id return_pmf"
by(simp add: rel_fun_def)

lemma cr_id_prob_bind [cr_id_prob_transfer]: 
  "(cr_id_prob A ===> (A ===> cr_id_prob B) ===> cr_id_prob B) bind_id bind_pmf"
by(auto simp add: rel_fun_def bind_return_pmf elim!: cr_id_prob.cases)

lemma cr_id_prob_Grp: "cr_id_prob (BNF_Def.Grp A f) = BNF_Def.Grp {x. set_id x \<subseteq> A} (return_pmf \<circ> f \<circ> extract)"
apply(auto simp add: Grp_def fun_eq_iff simp add: cr_id_prob.simps intro: id.expand)
subgoal for x by(cases x) auto
done

subsection \<open>State and Reader\<close>

text \<open>When no state updates are needed, the operation @{term get} can be replaced by @{term ask}.\<close>

named_theorems cr_envT_stateT_transfer

definition cr_prod1 :: "'c \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c \<Rightarrow> bool"
where "cr_prod1 c' A = (\<lambda>a (b, c). A a b \<and> c' = c)"

lemma cr_prod1_simps [simp]: "cr_prod1 c' A a (b, c) \<longleftrightarrow> A a b \<and> c' = c"
by(simp add: cr_prod1_def)

lemma cr_prod1I: "A a b \<Longrightarrow> cr_prod1 c' A a (b, c')" by simp

lemma cr_prod1_Pair_transfer [cr_envT_stateT_transfer]: "(A ===> eq_onp ((=) c) ===> cr_prod1 c A) (\<lambda>a _. a) Pair"
by(auto simp add: rel_fun_def eq_onp_def)

lemma cr_prod1_fst_transfer [cr_envT_stateT_transfer]: "(cr_prod1 c A ===> A) (\<lambda>a. a) fst"
by(auto simp add: rel_fun_def)

lemma cr_prod1_case_prod_transfer [cr_envT_stateT_transfer]:
  "((A ===> eq_onp ((=) c) ===> C) ===> cr_prod1 c A ===> C) (\<lambda>f a. f a c) case_prod"
by(simp add: rel_fun_def eq_onp_def)

lemma cr_prod1_Grp: "cr_prod1 c (BNF_Def.Grp A f) = BNF_Def.Grp A (\<lambda>b. (f b, c))"
by(auto simp add: Grp_def fun_eq_iff)


definition cr_envT_stateT :: "'s \<Rightarrow> ('m1 \<Rightarrow> 'm2 \<Rightarrow> bool) \<Rightarrow> ('s, 'm1) envT \<Rightarrow> ('s, 'm2) stateT \<Rightarrow> bool"
where "cr_envT_stateT s M m1 m2 = (eq_onp ((=) s) ===> M) (run_env m1) (run_state m2)"

lemma cr_envT_stateT_simps [simp]:
  "cr_envT_stateT s M (EnvT f) (StateT g) \<longleftrightarrow> M (f s) (g s)"
by(simp add: cr_envT_stateT_def rel_fun_def eq_onp_def)

lemma cr_envT_stateTE:
  assumes "cr_envT_stateT s M m1 m2"
  obtains f g where "m1 = EnvT f" "m2 = StateT g" "(eq_onp ((=) s) ===> M) f g"
using assms by(cases m1; cases m2; auto simp add: eq_onp_def)

lemma cr_envT_stateTD: "cr_envT_stateT s M m1 m2 \<Longrightarrow> M (run_env m1 s) (run_state m2 s)"
by(auto elim!: cr_envT_stateTE dest: rel_funD simp add: eq_onp_def)

lemma cr_envT_stateT_run [cr_envT_stateT_transfer]:
  "(cr_envT_stateT s M ===> eq_onp ((=) s) ===> M) run_env run_state"
by(rule rel_funI)(auto elim!: cr_envT_stateTE)

lemma cr_envT_stateT_StateT_EnvT [cr_envT_stateT_transfer]:
  "((eq_onp ((=) s) ===> M) ===> cr_envT_stateT s M) EnvT StateT"
by(auto 4 3 dest: rel_funD simp add: eq_onp_def)

lemma cr_envT_stateT_rec [cr_envT_stateT_transfer]:
  "(((eq_onp ((=) s) ===> M) ===> C) ===> cr_envT_stateT s M ===> C) rec_envT rec_stateT"
by(auto simp add: rel_fun_def elim!: cr_envT_stateTE)

lemma cr_envT_stateT_return [cr_envT_stateT_transfer]:
  notes [transfer_rule] = cr_envT_stateT_transfer shows
  "((cr_prod1 s A ===> M) ===> A ===> cr_envT_stateT s M) return_env return_state"
unfolding return_env_def return_state_def by transfer_prover

lemma cr_envT_stateT_bind [cr_envT_stateT_transfer]:
  "((M ===> (cr_prod1 s A ===> M) ===> M) ===> cr_envT_stateT s M ===> (A ===> cr_envT_stateT s M) ===> cr_envT_stateT s M)
   bind_env bind_state"
apply(rule rel_funI)+
apply(erule cr_envT_stateTE)
apply(clarsimp simp add: split_def)
apply(drule rel_funD)
 apply(erule rel_funD)
 apply(simp add: eq_onp_def)
apply(erule rel_funD)
apply(rule rel_funI)
apply clarsimp
apply(rule cr_envT_stateT_run[THEN rel_funD, THEN rel_funD, where B=M])
apply(erule (1) rel_funD)
apply(simp add: eq_onp_def)
done

lemma cr_envT_stateT_ask_get [cr_envT_stateT_transfer]:
  "((eq_onp ((=) s) ===> cr_envT_stateT s M) ===> cr_envT_stateT s M) ask_env get_state"
unfolding ask_env_def get_state_def
apply(rule rel_funI)+
apply simp
apply(rule cr_envT_stateT_run[THEN rel_funD, THEN rel_funD])
 apply(erule rel_funD)
 apply(simp_all add: eq_onp_def)
done

lemma cr_envT_stateT_fail [cr_envT_stateT_transfer]:
  notes [transfer_rule] = cr_envT_stateT_transfer shows
  "(M ===> cr_envT_stateT s M) fail_env fail_state"
unfolding fail_env_def fail_state_def by transfer_prover

subsection \<open>@{typ "_ spmf"} and @{typ "(_, _ prob) optionT"}\<close>

text \<open>
  This section defines the mapping between the @{typ "_ spmf"} monad and the monad obtained by
  composing transforming @{typ "_ prob"} with @{typ "(_, _) optionT"}.
\<close>

definition cr_spmf_prob_optionT :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'a option prob) optionT \<Rightarrow> 'b spmf \<Rightarrow> bool"
where "cr_spmf_prob_optionT A p q \<longleftrightarrow> rel_spmf A (run_option p) q"

lemma cr_spmf_prob_optionTI: "rel_spmf A (run_option p) q \<Longrightarrow> cr_spmf_prob_optionT A p q"
by(simp add: cr_spmf_prob_optionT_def)

lemma cr_spmf_prob_optionTD: "cr_spmf_prob_optionT A p q \<Longrightarrow> rel_spmf A (run_option p) q"
by(simp add: cr_spmf_prob_optionT_def)

lemma cr_spmf_prob_optionT_return_transfer:
   \<comment> \<open>Cannot be used as a transfer rule in @{method transfer_prover} because @{term return_spmf} is not a constant.\<close>
  "(A ===> cr_spmf_prob_optionT A) (return_option return_pmf) return_spmf"
by(simp add: rel_fun_def cr_spmf_prob_optionTI)

lemma cr_spmf_prob_optionT_bind_transfer:
  "(cr_spmf_prob_optionT A ===> (A ===> cr_spmf_prob_optionT A) ===> cr_spmf_prob_optionT A)
   (bind_option return_pmf bind_pmf) bind_spmf"
by(rule rel_funI cr_spmf_prob_optionTI)+
  (auto 4 4 simp add: run_bind_option bind_spmf_def dest!: cr_spmf_prob_optionTD dest: rel_funD intro: rel_pmf_bindI split: option.split)

lemma cr_spmf_prob_optionT_fail_transfer:
  "cr_spmf_prob_optionT A (fail_option return_pmf) (return_pmf None)"
by(rule cr_spmf_prob_optionTI) simp

abbreviation (input) spmf_of_prob_optionT :: "('a, 'a option prob) optionT \<Rightarrow> 'a spmf" 
where "spmf_of_prob_optionT \<equiv> run_option"

abbreviation (input) prob_optionT_of_spmf :: "'a spmf \<Rightarrow> ('a, 'a option prob) optionT"
where "prob_optionT_of_spmf \<equiv> OptionT"

lemma spmf_of_prob_optionT_transfer: "(cr_spmf_prob_optionT A ===> rel_spmf A) spmf_of_prob_optionT (\<lambda>x. x)"
by(auto simp add: rel_fun_def dest: cr_spmf_prob_optionTD)

lemma prob_optionT_of_spmf_transfer: "(rel_spmf A ===> cr_spmf_prob_optionT A) prob_optionT_of_spmf (\<lambda>x. x)"
by(auto simp add: rel_fun_def intro: cr_spmf_prob_optionTI)

end

section \<open>Monad homomorphisms\<close>

locale monad_hom = m1: monad return1 bind1 + m2: monad return2 bind2
  for return1 :: "('a, 'm1) return"
  and bind1 :: "('a, 'm1) bind"
  and return2 :: "('a, 'm2) return"
  and bind2 :: "('a, 'm2) bind"
  and h :: "'m1 \<Rightarrow> 'm2"
  +
  assumes hom_return: "\<And>x. h (return1 x) = return2 x"
  and hom_bind: "\<And>x f. h (bind1 x f) = bind2 (h x) (h \<circ> f)"
begin

lemma hom_lift [simp]: "h (m1.lift f m) = m2.lift f (h m)"
by(simp add: m1.lift_def m2.lift_def hom_bind hom_return o_def)

end

locale monad_fail_hom = m1: monad_fail return1 bind1 fail1 + m2: monad_fail return2 bind2 fail2 +
  monad_hom return1 bind1 return2 bind2 h
  for return1 :: "('a, 'm1) return"
  and bind1 :: "('a, 'm1) bind"
  and fail1 :: "'m1 fail"
  and return2 :: "('a, 'm2) return"
  and bind2 :: "('a, 'm2) bind"
  and fail2 :: "'m2 fail"
  and h :: "'m1 \<Rightarrow> 'm2"
  +
  assumes hom_fail [simp]: "h fail1 = fail2"

end
