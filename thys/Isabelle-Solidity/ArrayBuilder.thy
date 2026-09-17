theory ArrayBuilder
imports Solidity_Main Mcalc
begin

section \<open>Memory Array Building Contract\<close>
text \<open>
  In the following we verify the Memory Array Building contract,
  a contract implementing a common pattern in Solidity to leverage memory arrays to save gas costs.
  The contract is described further in
  \<^url>\<open>https://web.archive.org/web/20251024110129/https://fravoll.github.io/solidity-patterns/memory_array_building.html\<close>.
\<close>

subsection \<open>Formalisation of Contract\<close>

abbreviation "items \<equiv> STR ''items''"
abbreviation "owner \<equiv> STR ''owner''"
abbreviation "result  \<equiv> STR ''result''"
abbreviation "counter  \<equiv> STR ''counter''"
abbreviation "i \<equiv> STR ''i''"
abbreviation "itemCount \<equiv> STR ''itemCount''"
abbreviation "Item \<equiv> SType.TEnum [SType.TValue TAddress, SType.TValue (TBytes 32)]"

contract ArrayBuilder
  for items: "SType.DArray Item"
  and itemCount : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor payable
where
  "\<langle>skip\<rangle>"

cfunction getItems external payable
  param owner: "SType.TValue TAddress"
where
  "do {
    create_memory_array result (CType.TValue TSint) (itemCount  ~\<^sub>s [owner ~ []]);
    decl TSint counter;
    decl TSint i;
    while_monad ((i ~ []) \<langle><\<rangle> (storeArrayLength items []))
    (do {
      IF ((items ~\<^sub>s [i ~ [], \<langle>sint\<rangle> 0]) \<langle>=\<rangle> (owner ~ [])) THEN
        do {
          result [counter ~ []] ::= (i ~ []);
          counter [] ::= counter ~ [] \<langle>+\<rangle> \<langle>sint\<rangle> 1
        }
      ELSE
        \<langle>skip\<rangle>;
      i [] ::= i ~ [] \<langle>+\<rangle> \<langle>sint\<rangle> 1
    });
    r \<leftarrow> result ~ [];
    return r
  }"

subsection \<open>Specification of Invariant\<close>

text \<open>Trivial invariant to ensure type correctness\<close>

invariant myInv s
  where "length (storage_data.ar (fst s items)) < 2^256"
  for "ArrayBuilder"

text \<open>Alternative introduction Rule using existential quantification\<close>

lemma(in ArrayBuilder.arrayBuilder) myInvI2:
  assumes
    "\<exists>da. fst s items = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
          (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))"
      and "\<exists>mp. fst s itemCount = Map mp \<and> (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si))"
      and "length (storage_data.ar (fst s items)) < 2^256"
  shows "myInv s"
proof -
  have True by simp
  moreover from assms obtain da
    where "fst s items = storage_data.Array da"
      and "\<forall>y<length da.
            \<exists>em. da ! y = storage_data.Array em \<and>
              (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])"
    by auto
  moreover from assms obtain mp
    where "fst s itemCount = Map mp \<and> (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si))" by auto
  ultimately show ?thesis using myInvI assms(3) by blast
qed

subsection \<open>Filter Index Function\<close>

text \<open>The following function over lists is important to specify the postcondition.\<close>

fun filter_index_prefix_rec :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool" where
  "filter_index_prefix_rec 0 0 P xs ys = True"
| "filter_index_prefix_rec 0 (Suc y) P xs ys = False"
| "filter_index_prefix_rec (Suc x) 0 P xs ys =
    ((\<not> P (xs!x)) \<and> filter_index_prefix_rec x 0 P (butlast xs) [])"
| "filter_index_prefix_rec (Suc x) (Suc y) P xs ys =
    (if P (xs!x) then ys!y = x \<and> filter_index_prefix_rec x y P (butlast xs) (butlast ys)
    else filter_index_prefix_rec x (Suc y) P (butlast xs) ys)"

definition filter_index_prefix where
  "filter_index_prefix P xs ys \<equiv> filter_index_prefix_rec (length xs) (length ys) P xs ys"

definition filter_index where
  "filter_index P xs ys \<equiv> filter_index_prefix P xs ys"

text \<open>Some examples\<close>

lemma "filter_index ((=) True) [True] [0] = True" by eval
lemma "filter_index ((=) True) [False] [1,2] = False" by eval
lemma "filter_index ((=) True) [False] [] = True" by eval
lemma "filter_index ((=) True) [False,True,False,True,False] [1,3] = True" by eval
lemma "filter_index ((=) True) [False,True,False,True,False] [1,2] = False" by eval

text \<open>Lemmas\<close>

lemma length_filter_take_p:
  assumes "n < length x"
      and "P (x ! n)"
    shows "length (filter P (take n x)) < length (filter P x)"
  using assms
proof (induction x arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Cons.prems(2) by auto
  next
    case (Suc nat)
    then have "nat < length (x)" using Cons.prems(1) by auto
    moreover have "P (x ! nat)" using Cons.prems(2) Suc by auto
    ultimately have "length (filter P (take nat x)) < length (filter P x)" using Cons.IH by blast
    then show ?thesis by (simp add: Suc)
  qed
qed

lemma length_filter_take_np:
  assumes "n < length a"
      and "\<not> P (a!n)"
    shows "length (filter P (take n a)) = length (filter P (take (Suc n) a))"
  using assms
proof (induction a arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Cons.prems(2) by auto
  next
    case (Suc nat)
    then have "nat < length (x)"
      using Cons.prems(1) by auto
    moreover have "\<not> P (x ! nat)"
      using Cons.prems(2) Suc by auto
    ultimately have "length (filter P (take nat x)) = length (filter P (take (Suc nat) x))"
      using Cons.IH by blast
    then show ?thesis by (simp add: Suc)
  qed
qed

lemma filter_index_prefix_rec_P:
  assumes "filter_index_prefix_rec (length xs) (length ys) P xs ys"
      and "P x"
    shows "filter_index_prefix_rec (Suc (length xs)) (Suc (length ys)) P (xs @ [x]) (ys @ [length xs])"
  using assms by simp

lemma filter_index_prefix_rec_not_P:
  assumes "filter_index_prefix_rec (length xs) (length ys) P xs ys"
      and "\<not> P x"
    shows "filter_index_prefix_rec (Suc (length xs)) (length ys) P (xs @ [x]) ys"
  using assms by (cases ys,auto)

subsection \<open>Pre/Postcondition\<close>

definition(in Contract) filter_items where
"filter_items state ow =
  filter_index
    (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow)
    (storage_data.ar (state.Storage state this items))"

definition(in Contract) filter_items_prefix where
"filter_items_prefix n it ow =
  filter_index_prefix
    (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow)
    (take n (storage_data.ar it))"

(*
v'a = index i
ar = static version of memory array result
ad = address of owner of item i which is the same as owner parameter
v' = value of counter
daa = items array
*)
lemma (in Contract) filter_items_prefix_suc_eq:
  fixes ad ar
  defines "filter_pred x \<equiv> valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad"
  assumes
    "filter_items_prefix (unat v'a) (storage_data.Array daa) ad
      (map (unat \<circ> valtype.uint \<circ> adata.vt)
        (take (length (filter filter_pred (take (unat v'a) daa))) ar))"
      and "unat v'a < length daa"
      and "length (filter filter_pred daa) = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "length (filter filter_pred (take (unat v'a) daa)) \<le> unat v'a"
      and "unat v' = length (filter filter_pred (take (unat v'a) daa))"
      and "length ar = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "daa $ unat v'a \<bind> slookup [Uint 0] = Some yb"
      and "storage_data.vt yb = Address ad"
      and "length daa < 2^256"
      and
       "\<forall>y<length daa.
         \<exists>em. daa ! y = storage_data.Array em \<and>
          (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])"
    shows
       "\<exists>ara. the (aupdate [Uint v'] (adata.Value (Uint v'a)) (adata.Array ar)) = adata.Array ara \<and>
         filter_items_prefix (unat (v'a + 1))
           (storage_data.Array daa)
             ad (map (unat \<circ> valtype.uint \<circ> adata.vt) (take (unat (v' + 1)) ara))"
proof -
  from assms(3,11) obtain em ad0 bt0
    where *: "daa ! unat v'a = storage_data.Array em"
      and **: "em = [storage_data.Value (Address ad0), storage_data.Value (Bytes bt0)]"
  by auto

  from assms(3,8,9,11)
    have ***: "valtype.ad (storage_data.vt (hd (storage_data.ar (daa ! unat v'a)))) = ad"
    by auto
  then have "unat v' < length ar"
    using length_filter_take_p[where ?P="filter_pred", of "(unat v'a)" daa] assms(3,4,6,7)
    unfolding filter_pred_def by linarith
  then have
    "length (filter filter_pred (take (unat v'a) daa))
      < unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
    using assms by argo
  moreover have
    "filter_items_prefix (unat (v'a + 1)) (storage_data.Array daa) ad
      (map (unat \<circ> valtype.uint \<circ> adata.vt)
        (take (unat (v' + 1))
          (ar[length (filter filter_pred (take (unat v'a) daa)) := adata.Value (Uint v'a)])))"
  proof -
    from assms(2) have
      "filter_index_prefix_rec
        (length (take (unat v'a) (storage_data.ar (storage_data.Array daa))))
        (length
          (map (unat \<circ> valtype.uint \<circ> adata.vt)
           (take (length (filter filter_pred (take (unat v'a) daa))) ar)))
        filter_pred
        (take (unat v'a) (storage_data.ar (storage_data.Array daa)))
        (map (unat \<circ> valtype.uint \<circ> adata.vt)
          (take (length (filter filter_pred (take (unat v'a) daa))) ar))"
      unfolding filter_items_prefix_def filter_index_prefix_def filter_pred_def
      by blast
    moreover have "valtype.ad (storage_data.vt (hd (em))) = ad" using * *** by auto
    ultimately have
      "filter_index_prefix_rec
        (Suc (length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))))
        (Suc (length
          (map (unat \<circ> valtype.uint \<circ> adata.vt)
            (take (length (filter filter_pred (take (unat v'a) daa))) ar))))
        filter_pred
        (take (unat v'a) (storage_data.ar (storage_data.Array daa)) @ [storage_data.Array em])
        (map (unat \<circ> valtype.uint \<circ> adata.vt)
          (take (length (filter filter_pred (take (unat v'a) daa))) ar) @
          [length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))])"
    using filter_index_prefix_rec_P[where ?P = "filter_pred"] * ***
    unfolding filter_pred_def by presburger
    moreover have
      "length (take (unat (v'a + 1)) (storage_data.ar (storage_data.Array daa)))
     = Suc (length (take (unat v'a) (storage_data.ar (storage_data.Array daa))))"
      using assms(3,10) unat_add_lem[where ?'a=256, of v'a 1] by (simp add:wpsimps)
    moreover have
      "length
         (map (unat \<circ> valtype.uint \<circ> adata.vt)
           (take (unat (v' + 1))
             (ar[length (filter filter_pred (take (unat v'a) daa)) := adata.Value (Uint v'a)])))
     = Suc (length
         (map (unat \<circ> valtype.uint \<circ> adata.vt)
           (take (length (filter filter_pred (take (unat v'a) daa))) ar)))"
    proof -
      from assms(4,7,10) have "length ar < 2 ^ 256"
        using length_filter_le[of "filter_pred" daa] by auto
      then show ?thesis
        using assms(6) \<open>unat v' < length ar\<close> unat_add_lem[where ?'a=256, of v' 1]
        by (simp add:wpsimps)
    qed
    moreover have
      "take (unat (v'a + 1)) (storage_data.ar (storage_data.Array daa))
     = take (unat v'a) (storage_data.ar (storage_data.Array daa)) @ [storage_data.Array em]"
    proof -
      from assms * **
        have "storage_data.ar (storage_data.Array daa) ! unat v'a = storage_data.Array em"
        by simp
      then show ?thesis
        using assms(3,10)
          take_Suc_conv_app_nth[of "unat v'a" "(storage_data.ar (storage_data.Array daa))"]
          unat_add_lem[where ?'a=256, of v'a 1]
        by (simp add:wpsimps)
    qed
    moreover have
      "map (unat \<circ> valtype.uint \<circ> adata.vt)
         (take (length (filter filter_pred (take (unat v'a) daa))) ar) @
           [length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))]
     = map (unat \<circ> valtype.uint \<circ> adata.vt)
         (take (unat (v' + 1))
           (ar[length (filter filter_pred (take (unat v'a) daa)) := adata.Value (Uint v'a)]))"
    proof -
      from assms(4,7,10) have "length ar < 2 ^ 256"
        using length_filter_le[of "filter_pred" daa]
        by auto
      then show ?thesis
        using \<open>unat v' < length ar\<close>
          upd_conv_take_nth_drop[of "unat v'" ar]
          unat_add_lem[where ?'a=256, of v' 1]
          assms(3,6)
        by (simp add:wpsimps)
    qed
    ultimately show ?thesis
      unfolding filter_items_prefix_def filter_index_prefix_def filter_pred_def
      by argo
  qed
  ultimately show ?thesis using assms by (auto simp add:nth_safe_def)
qed

definition(in Contract) allItems where
"allItems xs ow =
  [x \<leftarrow> xs. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow]"

definition(in Contract) getItems_pre where
  "getItems_pre ow start_state \<equiv>
    length (allItems (storage_data.ar (state.Storage start_state this items)) ow)
    = unat (valtype.uint (storage_data.vt
        (storage_data.mp (state.Storage start_state this itemCount) (valtype.Address ow))))"

definition(in Contract) getItems_post where
  "getItems_post ow start_state return_value end_state \<equiv>
    pred_some
      (\<lambda>xs. filter_items end_state ow (map (unat \<circ> valtype.uint \<circ> adata.vt) (adata.ar xs)))
      (aread (State.Memory end_state) (rvalue.memloc return_value))"

lemma (in Contract) filter_items_prefix_suc_neq:
  fixes ad ar x a
  defines
    "xs \<equiv>
      map
        (unat \<circ> valtype.uint \<circ> adata.vt)
        (take
          (length
            (filter
              (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad)
              (take (unat x) a)))
          ar)"
    and "filter_predicate \<equiv> \<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad"
  assumes "length a < 2^256"
    and "unat (x::256 word) < length a"
    and "filter_items_prefix (unat x) (storage_data.Array a) ad xs"
    and "a ! unat x = storage_data.Array [storage_data.Value (Address ada), storage_data.Value (Bytes bt)]"
    and "ada \<noteq> ad"
  shows "filter_items_prefix (unat (x + 1)) (storage_data.Array a) ad xs"
proof -
  from assms(1,2,5) have
    "filter_index_prefix_rec (length (take (unat x) a)) (length xs) filter_predicate (take (unat x) a) xs"
    by (simp add:filter_items_prefix_def filter_index_prefix_def)
  moreover from assms(6,7)
    have "valtype.ad (storage_data.vt (hd (storage_data.ar (a ! unat x)))) \<noteq> ad"
    by auto
  ultimately have
    "filter_index_prefix_rec
      (Suc (length (take (unat x) a))) (length xs) filter_predicate (take (unat x) a @ [a ! unat x]) xs"
    using assms(1,2) filter_index_prefix_rec_not_P [of "(take (unat x) a)" xs] by auto
  moreover from assms(3,4) have
    "take (unat x) a @ [a ! unat x] = take (unat (x + 1)) (storage_data.ar (storage_data.Array a))"
    using unat_add_lem[where ?'a=256, of x 1] take_Suc_conv_app_nth[of "unat x" a] by auto
  ultimately show ?thesis
    unfolding filter_items_prefix_def filter_index_prefix_def
    using assms(1,2,3,4) unat_add_lem[where ?'a=256, of x 1]
    by auto
qed

subsection \<open>While Invariant\<close>
definition(in Contract) while_inv2 where
  "while_inv2 state \<equiv>
    (\<exists>x. state.Stack state $$ owner = Some (kdata.Value x))
    \<and> (\<exists>ml. state.Stack state $$ result = Some (kdata.Memory ml)
        \<and> ml < length (state.Memory state)
        \<and> (\<exists>ma0. state.Memory state ! ml = mdata.Array ma0
            \<and> (\<forall>i<length ma0. (ma0 ! i) < length (state.Memory state) \<and> (\<exists>ix. state.Memory state ! (ma0!i) = mdata.Value (valtype.Uint ix)))))
    \<and> (\<exists>x. state.Stack state $$ i = Some (kdata.Value (valtype.Uint x)))
    \<and> (\<exists>x. state.Stack state $$ counter = Some (kdata.Value (valtype.Uint x)))
    \<and> length (storage_data.ar (state.Storage state this items)) < 2^256
    \<and> (\<exists>da. (state.Storage state this items) = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])))
    \<and> (\<exists>mp. state.Storage state this itemCount = Map mp \<and>
        (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)))"

definition(in Contract) while_inv where
  "while_inv own state \<equiv>
    while_inv2 state
    \<and> arange (state.Memory state) (kdata.memloc (state.Stack state $$! result)) = Some (the (arange (state.Memory state) (kdata.memloc (state.Stack state $$! result))))
    \<and> length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own)) = unat (valtype.uint (storage_data.vt (storage_data.mp (state.Storage state this itemCount) own)))
    \<and> pred_some (\<lambda>xs. \<exists>ar. xs = adata.Array ar \<and> filter_items_prefix (unat (valtype.uint (kdata.vt (state.Stack state $$! i)))) (state.Storage state this items) (valtype.ad (kdata.vt (state.Stack state $$! owner))) (map (unat \<circ> valtype.uint \<circ> adata.vt) (take (unat (valtype.uint (kdata.vt (state.Stack state $$! counter)))) ar))) (aread (State.Memory state) (kdata.memloc (state.Stack state $$! result)))
    \<and> adisjoint (state.Memory state) (the (arange (state.Memory state) (kdata.memloc (state.Stack state $$! result))))
    \<and> state.Stack state $$ owner = Some (kdata.Value own)
    \<and> pred_some (\<lambda>xs. length (adata.ar xs) = length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own))) (aread (State.Memory state) (kdata.memloc (state.Stack state $$! result)))
    \<and> unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) = length (allItems (take (unat (valtype.uint (kdata.vt (state.Stack state $$! i)))) (storage_data.ar (state.Storage state this items))) (valtype.ad own))
    \<and> unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) \<le> unat (valtype.uint (kdata.vt (state.Stack state $$! i)))"

lemma(in Contract) while_init:
  assumes "unat (valtype.uint (kdata.vt (state.Stack state $$! i))) = 0"
      and "unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) = 0"
      and "adisjoint (state.Memory state) (the (arange (state.Memory state) (kdata.memloc (state.Stack state $$! result))))"
      and "state.Stack state $$ owner = Some (kdata.Value own)"
      and "length (storage_data.ar (state.Storage state this items)) < 2^256"
      and "pred_some (\<lambda>xs. length (adata.ar xs) = length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own))) (aread (State.Memory state) (kdata.memloc (state.Stack state $$! result)))"
      and "(\<exists>ml. state.Stack state $$ result = Some (kdata.Memory ml)
            \<and> ml < length (state.Memory state)
            \<and> (\<exists>ma0. state.Memory state ! ml = mdata.Array ma0
                \<and> (\<forall>i<length ma0. (ma0 ! i) < length (state.Memory state) \<and> (\<exists>ix. state.Memory state ! (ma0!i) = mdata.Value (valtype.Uint ix)))))"
      and "(\<exists>x. state.Stack state $$ i = Some (kdata.Value (valtype.Uint x)))"
      and "(\<exists>x. state.Stack state $$ counter = Some (kdata.Value (valtype.Uint x)))"
      and "aread
            (state.Memory state)
            (kdata.memloc (Stack state $$! result))
          = Some (adata.Array (array (unat si) (adata.Value (Uint 0))))"
      and "(\<exists>da. (state.Storage state this items) = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])))"
      and "(\<exists>mp. state.Storage state this itemCount = Map mp \<and>
        (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)))"
      and "arange (state.Memory state) (kdata.memloc (state.Stack state $$! result)) = Some (the (arange (state.Memory state) (kdata.memloc (state.Stack state $$! result))))"
      and "length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own)) = unat (valtype.uint (storage_data.vt (storage_data.mp (state.Storage state this itemCount) own)))"
    shows "while_inv own state"
  using assms unfolding while_inv_def while_inv2_def
  by (simp add:pred_some_def filter_items_prefix_def filter_index_prefix_def allItems_def)

lemma(in Contract) while_init2:
  assumes "\<exists>x. state.Stack state $$ owner = Some (kdata.Value x)"
      and "length (storage_data.ar (state.Storage state this items)) < 2^256"
      and "(\<exists>ml. state.Stack state $$ result = Some (kdata.Memory ml)
            \<and> ml < length (state.Memory state)
            \<and> (\<exists>ma0. state.Memory state ! ml = mdata.Array ma0
                \<and> (\<forall>i<length ma0. (ma0 ! i) < length (state.Memory state) \<and> (\<exists>ix. state.Memory state ! (ma0!i) = mdata.Value (valtype.Uint ix)))))"
      and "(\<exists>x. state.Stack state $$ i = Some (kdata.Value (valtype.Uint x)))"
      and "(\<exists>x. state.Stack state $$ counter = Some (kdata.Value (valtype.Uint x)))"
      and "(\<exists>da. (state.Storage state this items) = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])))"
      and "(\<exists>mp. state.Storage state this itemCount = Map mp \<and>
        (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)))"
    shows "while_inv2 state"
  using assms unfolding while_inv2_def
  by (simp add:pred_some_def filter_items_prefix_def filter_index_prefix_def allItems_def)

lemma (in Contract) while_inv_post:
  assumes "while_inv sstate end_state"
      and "ow = valtype.ad (kdata.vt (state.Stack end_state $$! owner))"
      and "rvalue.memloc return_value = kdata.memloc (state.Stack end_state $$! result)"
      and "unat (valtype.uint (kdata.vt (state.Stack end_state $$! i))) \<ge> (length (storage_data.ar (state.Storage end_state this items)))"
    shows "getItems_post ow start_state return_value end_state"
  using assms unfolding while_inv_def getItems_post_def allItems_def pred_some_def filter_items_def filter_items_prefix_def filter_index_def
  by (auto intro: length_filter_le take_all_iff split:option.split_asm option.split)

subsection \<open>Other\<close>

lemma kdequals_x_True[wpdrules]:
  assumes "kdequals yc (rvalue.Value (Bool True)) = Some (rvalue.Value (Bool False))"
    shows "yc = rvalue.Value (Bool False)"
  using assms unfolding kdequals_def
  apply (cases yc,auto)
  by (case_tac x4,auto)

lemma kdequals_address_False[wpdrules]:
    fixes ad
  assumes "kdequals (rvalue.Value (Address ada)) (rvalue.Value (Address ad)) = Some (rvalue.Value (Bool False))"
    shows "ada \<noteq> ad"
  using assms unfolding kdequals_def
  by auto

lemma kdequals_True[wpdrules]:
  assumes "kdequals x y = Some (rvalue.Value (Bool True))"
    shows "x = y"
  using assms unfolding kdequals_def
  apply (cases x,auto)
  apply (cases y,auto)
  apply (case_tac x4a,auto)
  by (case_tac x4,auto)+

lemma kdplus_safe_value_value:     
  assumes "kdplus_safe (rvalue.Value v) (rvalue.Value (Uint 1)) = Some y"
  obtains v'
    where "v = Uint v'"
      and "y = rvalue.Value (Uint (v' + 1))"
      and "unat v' + unat 1 < 2^256"
  using assms unfolding kdplus_safe_def
  apply (cases v)
  by (auto simp add:wpsimps vtplus_safe.simps split:if_split_asm)

lemma kdless_uint_length_false:
  assumes
    "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint (word_of_nat (length a)::256 word)))
      = Some (rvalue.Value (Bool False))"
      and "length a<2^256"
    shows "\<not> unat x < length a"
  using assms unfolding kdless_def vtless_def
proof (cases "x <  ((word_of_nat (length a))::256 word)", auto)
  assume "\<not> x < ((word_of_nat (length a))::256 word)" and *: "unat x < length a"
  then have "((word_of_nat (length a))::256 word) \<le> x" by simp
  then have "unat ((word_of_nat (length a))::256 word) \<le> unat x"
    by (simp add: word_le_nat_alt[where ?'a =256])
  moreover from assms(2) have "length a\<le>unat (2^256-1::256 word)" by simp
  ultimately have "length a \<le> unat x"
    using le_unat_uoi[where ?'a =256, of "length a" _] assms(2) by metis
  then show False using * by simp
qed

lemma kdless_uint_length_true:
  assumes
    "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint (word_of_nat (length a)::256 word)))
      = Some (rvalue.Value (Bool True))"
    and "length a<2^256"
  shows "unat x < length a"
  using assms unfolding kdless_def vtless_def
proof (cases "x < ((word_of_nat (length a))::256 word)",auto)
  assume "x < ((word_of_nat (length a))::256 word)"
  then have "unat x < (unat ((word_of_nat (length a))::256 word))"
    by (simp add: word_less_nat_alt[where ?'a =256])
  moreover from assms(2) have "length a\<le>unat (2^256-1::256 word)" by simp
  ultimately have "unat x < length a"
    using le_unat_uoi[where ?'a =256, of "length a" _] assms(2) by metis
  then show "unat x < length a" by simp
qed

lemma (in Contract) updateCalldata_length:
  fixes ar ad
  defines "filter_pred x \<equiv> valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad"
  assumes "unat v'a < length daa"
      and "length (filter filter_pred daa) = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "unat v' = length (filter filter_pred (take (unat v'a) daa))"
      and "length ar = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "daa $ unat v'a \<bind> slookup [Uint 0] = Some yb"
      and "storage_data.vt yb = Address ad"
      and "\<forall>y<length daa.
             \<exists>em. daa ! y = storage_data.Array em \<and>
              (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])"
  shows "length (adata.ar (the (aupdate [Uint v'] (adata.Value (Uint v'a)) (adata.Array ar)))) =
          unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
proof -
  from assms(2,6,7,8)
    have "valtype.ad (storage_data.vt (hd (storage_data.ar (daa ! unat v'a)))) = ad"
    by auto
  then have "unat v' < length ar"
    using length_filter_take_p[where ?P="filter_pred", of "(unat v'a)" daa] assms(2,3,4,5)
    unfolding filter_pred_def by linarith
  then show ?thesis using assms(5) by auto
qed

lemma (in Contract) length_filter_take_np_2:
  fixes ad
  assumes "length a < 2^256"
      and "unat (x::256 word) < length a"
      and "a ! unat x = storage_data.Array [storage_data.Value (Address ada), storage_data.Value (Bytes bt)]"
      and "ada \<noteq> ad"
    shows "length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a))
           = length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat (x + 1)) a))"
  using assms
    length_filter_take_np[of "unat x" a "(\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad)"]
    unat_add_lem[where ?'a=256, of x 1]
  by auto

lemma (in Contract) length_filter_le_2:
  fixes ad
  assumes "length a < 2^256"
      and "unat (x::256 word) < length a"
    shows "length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a)) \<le> unat (x + 1)"
  using assms
    unat_add_lem[where ?'a=256, of x 1]
    length_filter_le[of "\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad" "(take (unat x) a)"]
    length_take[of "unat x" a]
  by auto

lemma (in Contract) length_filter_take:
  fixes ad
  assumes "daa ! unat v'a = storage_data.Array [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]"
      and "unat (v'a::256word) < length daa"
      and "length daa < 2^256"
      and "unat (v'::256word) = length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat v'a) daa))"
      and "length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat v'a) daa))
         \<le> unat v'a"
  shows "unat (v' + 1)
    = length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat (v'a + 1)) daa))"
  using length_filter_take_suc[of "unat v'a" daa "(\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad)"]
    unat_add_lem[where ?'a=256, of v'a 1]
    unat_add_lem[where ?'a=256, of v' 1]
    assms(1,2,3,4,5)
  by auto

lemma unat_le_unat_suc:
  fixes ad
  assumes "unat (v'::256 word) \<le> unat v'a"
      and "length daa < 2^256"
      and "unat (v'a::256 word) < length daa"
    shows "unat (v' + 1) \<le> unat (v'a + 1)"
using assms unat_add_lem[where ?'a=256, of v'a 1] unat_add_lem[where ?'a=256, of v' 1] by simp

lemma pred_someE:
  assumes "pred_some P v"
  obtains v' where "v = Some v'" and "P v'"
  using assms unfolding pred_some_def by blast

subsection \<open>Verifying the Contract\<close>

verification sum_votes:
  myInv
  getItems (getItems_pre, getItems_post)
  for "ArrayBuilder"
proof -

  show
    "\<And>call.
      effect (constructor call) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> post s r (K (K (inv_state myInv))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply wp+
    by (auto simp add: wpsimps)

  show
    "\<And>call ad.
      effect (getItems call ad) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state myInv s
      \<Longrightarrow> post s r (K (K (inv_state myInv))) (K True)"
    unfolding getItems_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (erule myInvE)
    apply (erule conjE)+
    apply wp+
          defer
          defer
          apply wp+
     defer
     apply wp+
    apply (rule_tac P = "\<lambda>y. \<exists>si. mp y = storage_data.Value (Uint si)" and x = y in allE,assumption)
    apply (rule_tac exE,assumption)
    apply wp+
    apply (rule_tac iv="while_inv2" in wpwhile)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
           apply (simp add: while_inv2_def)
          apply (simp add: while_inv2_def)
         apply (simp add: while_inv2_def)
        defer
        apply (simp add: while_inv2_def)
       apply (simp add: while_inv2_def)
      apply (simp add: while_inv2_def)
     defer
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply wp
       apply wp
       apply wp
       apply wp
      defer
      apply wp
      apply wp
      apply wp
     defer
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply wp
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply (safe)[1]
    (*
      3 Goals left
      - whileinv is preserved during execution
      - whileinv implies postcondition
      - whileinv is established
    *)
      defer
    (*Whileinv establishes postcondition*)
      apply wp
      apply wp
      apply wp
      apply wp
            apply (simp add: while_inv2_def)
           defer
           apply (simp add: while_inv2_def)
          apply (simp add: while_inv2_def)
         apply (simp add: while_inv2_def)
        apply (simp add: while_inv2_def)
       apply (simp add: while_inv2_def)
      defer
      defer
      apply wp
      apply wp
       defer
       apply wp
       apply wp
      defer
      defer
      apply wp
      apply wp
       defer
       apply wp
       apply wp
      defer
      defer
      apply wp
       apply wp
       apply (auto simp add: wpsimps while_inv2_def mlookup.simps)[1]
      apply wp
      apply (rule myInvI2)
        apply (simp add: while_inv2_def)
       apply (simp add: while_inv2_def)
      apply (simp add: while_inv2_def)
    (*Whileinv is established*)
     apply (rule while_init2)
           apply (simp add: wpsimps)
          apply (simp add: wpsimps)
         defer
         defer
         apply (simp add: wpsimps)
        defer
        defer
        defer
        apply (simp add: wpsimps write_array_typing_value)
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     apply (simp add: wpsimps)
    (*Whileinv is preserved*)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp)
         apply (simp)
        apply (simp)
       defer
       apply (simp)
      apply (simp)
     apply (simp)
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
     defer
     apply (auto simp add: wpsimps while_inv2_def)[1]
     apply (erule_tac P= "\<lambda>y. y < length a \<longrightarrow> (\<exists>em. a ! y = storage_data.Array em \<and> (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))" in allE)
     apply (auto simp add: nth_safe_def split:if_split_asm)[1]
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: while_inv2_def)
         apply (simp add: while_inv2_def)
        apply (simp add: while_inv2_def)
       defer
       apply (simp add: while_inv2_def)
      apply (simp add: while_inv2_def)
     apply (simp add: while_inv2_def)
    apply wp
    apply wp
     defer
     apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply wp
    apply wp
     defer
     apply wp
      defer
      apply wp
      apply wp
    (*2 subgoals: if is true and if is false*)
     defer
    (**If condition is false**)
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
           apply (simp)
          apply (simp)
         apply (simp)
        defer
        apply (simp)
       apply (simp)
      apply (simp)
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
           apply (simp)
          apply (simp)
         apply (simp)
        defer
        apply (simp)
       apply (simp)
      apply (simp)
     apply wp
     apply wp
     apply wp
     apply wp
      defer
      apply wp
      apply wp
     defer
     apply wp
     apply wp
     apply wp
     apply (erule kdplus_safe_value_value)
     apply simp
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
     apply (rule wp_assign_stack_kdvalue)
           apply (simp)
          apply (simp)
         apply (simp)
        apply (simp)
       apply (simp)
      defer
      apply (simp)
     defer
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply (simp add: wpsimps while_inv2_def)
    (**If condition is true**)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: while_inv2_def)
         apply (simp add: while_inv2_def)
        apply (simp add: while_inv2_def)
       defer
       apply (simp add: while_inv2_def)
      apply (simp add: while_inv2_def)
     apply (simp add: while_inv2_def)
    apply wp
    apply wp
    apply wp
     defer
     apply wp
     apply wp
    apply wp
    apply wp
    apply (simp only:while_inv2_def)
    apply safe
    apply wp
      apply wp
      apply wp
     apply wp
     apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: while_inv2_def)
         apply (simp add: while_inv2_def)
        apply (simp add: while_inv2_def)
       defer
       apply (simp add: while_inv2_def)
      apply (simp add: while_inv2_def)
     apply (simp add: while_inv2_def)
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    apply (erule kdplus_safe_value_value)
    apply simp
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
          apply (simp)
         apply (simp)
        apply (simp)
       apply (simp)
      apply (simp)
    defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: wpsimps)
         apply (simp add: wpsimps)
        apply (simp add: wpsimps)
       defer
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     apply (simp add: wpsimps)
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply wp
    apply wp
    apply wp
    apply (erule kdplus_safe_value_value)
    apply (simp)
    apply (rule wp_assign_stack_kdvalue)
          apply (simp)
         apply (simp add: wpsimps)
        apply (simp add: wpsimps)
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     defer
     apply (simp add: wpsimps)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp only:while_inv2_def)
    apply safe
          apply (simp add: wpsimps)
         defer
         apply (simp add: wpsimps)
        apply (simp add: wpsimps)
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     apply (simp add: wpsimps)
     apply (simp add: wpsimps mupdate_array_typing_value)
    by (metis mvalue_update_length)

  show
    "\<And>call ad.
      effect (getItems call ad) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state myInv s
      \<Longrightarrow> getItems_pre ad s
      \<Longrightarrow> post s r (getItems_post ad) (K True)"
    unfolding getItems_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (erule myInvE)
    apply (erule conjE)+
    apply wp+
          defer
          defer
          apply wp+
     defer
     apply wp+
    apply (rule_tac P = "\<lambda>y. \<exists>si. mp y = storage_data.Value (Uint si)" and x = y in allE,assumption)
    apply (rule_tac exE,assumption)
    apply wp+
    apply (rule_tac iv="while_inv y" in wpwhile)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
     apply (wp)
           apply (simp add: while_inv_def while_inv2_def)
          apply (simp add: while_inv_def while_inv2_def)
         apply (simp add: while_inv_def while_inv2_def)
        defer
        apply (simp add: while_inv_def while_inv2_def)
       apply (simp add: while_inv_def while_inv2_def)
      apply (simp add: while_inv_def while_inv2_def)
     defer
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply wp
       apply wp
       apply wp
       apply wp
      defer
      apply wp
      apply wp
      apply wp
     defer
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply wp
     apply wp
     apply wp
      defer
      apply wp
     defer
     apply (safe)[1]
    (*
      3 Goals left
      - whileinv is preserved during execution
      - whileinv implies postcondition
      - whileinv is established
    *)
      defer
    (*Whileinv establishes postcondition*)
      apply wp
      apply wp
      apply wp
      apply wp
            apply (simp add: while_inv_def while_inv2_def)
           defer
           apply (simp add: while_inv_def while_inv2_def)
          apply (simp add: while_inv_def while_inv2_def)
         apply (simp add: while_inv_def while_inv2_def)
        apply (simp add: while_inv_def while_inv2_def)
       apply (simp add: while_inv_def while_inv2_def)
      defer
      defer
      apply wp
      apply wp
       defer
       apply wp
       apply wp
      defer
      defer
      apply wp
      apply wp
       defer
       apply wp
       apply wp
      defer
      defer
      apply wp
       apply (auto simp add: wpsimps while_inv_def while_inv2_def mlookup.simps nth_safe_def split:if_split_asm)[1]
      apply wp
      apply wp
      apply (rule while_inv_post,assumption)
        apply (simp add: while_inv_def)
       apply (simp add:mlookup.simps)
      apply (simp add: while_inv_def while_inv2_def)[1]
      apply safe
      apply (drule kdless_uint_length_false)
       apply (simp)
      apply (simp)
    (*Whileinv is established*)
     apply (rule while_init)
                  apply (simp add: wpsimps)
                 apply (simp add: wpsimps)
                apply (simp add: wpsimps)
                apply mc
               apply (simp add: wpsimps)
              apply (simp add: wpsimps allItems_def getItems_pre_def)
             defer
             defer
             apply (simp add: wpsimps)
            apply (simp add: wpsimps)
           defer
           defer
           apply (simp add: wpsimps)
          apply (simp add: wpsimps)
          apply mc
         apply (simp add: wpsimps getItems_pre_def)
        defer
        apply (simp add: wpsimps allItems_def getItems_pre_def)
        apply (rule pred_some_read)
         apply mc+
        apply (simp)
       apply (simp add: wpsimps write_array_typing_value)
      defer
      apply (simp add: wpsimps)
     apply (simp add: wpsimps)
     defer
     apply (simp add: wpsimps)
     apply mc
    (*Whileinv is preserved*)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp)
         apply (simp)
        apply (simp)
       defer
       apply (simp)
      apply (simp)
     apply (simp)
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
     defer
     apply (auto simp add: wpsimps while_inv_def while_inv2_def nth_safe_def split:if_split_asm)[1]
     apply (erule_tac P= "\<lambda>y. y < length a \<longrightarrow> (\<exists>em. a ! y = storage_data.Array em \<and> (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))" in allE)
     apply auto
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: while_inv_def)
         apply (simp add: while_inv_def)
        apply (simp add: while_inv_def)
       defer
       apply (simp add: while_inv_def)
      apply (simp add: while_inv_def)
     apply (simp add: while_inv_def)
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply wp
    (*2 subgoals: if is true and if is false*)
     defer
     apply wp
      defer
      apply wp
      apply wp
     defer
    (**If condition is false**)
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
           apply (simp)
          apply (simp)
         apply (simp)
        defer
        apply (simp)
       apply (simp)
      apply (simp)
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
           apply (simp add: wpsimps)
          apply (simp add: wpsimps)
         apply (simp add: wpsimps)
        defer
        apply (simp add: wpsimps)
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     apply wp
     apply wp
     apply wp
     apply wp
      defer
      apply wp
      apply wp
     defer
     apply wp
     apply wp
     apply wp
     apply (auto simp add: while_inv_def while_inv2_def)[1]
     apply wp
     apply wp
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
     apply (rule wp_assign_stack_kdvalue)
           apply (simp)
          apply (simp)
         apply (simp)
        apply (simp)
       apply (simp)
      defer
      apply (simp)
     defer
     apply wp
     apply wp
     apply wp
     apply wp
     apply wp
     apply (auto simp add: wpsimps while_inv_def while_inv2_def allItems_def)[1]
       apply (erule pred_someE)
       apply (rule pred_some_read,assumption)
       apply (drule kdless_uint_length_true)
        apply simp
       apply (erule_tac P= "\<lambda>y. y < length a \<longrightarrow> (\<exists>em. a ! y = storage_data.Array em \<and> (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))" in allE)
       apply (auto)[1]
       apply wp+
       apply (simp add: filter_items_prefix_suc_neq)
      apply (drule kdless_uint_length_true)
       apply simp
      apply simp
      apply (erule_tac P= "\<lambda>y. y < length a \<longrightarrow> (\<exists>em. a ! y = storage_data.Array em \<and> (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))" in allE)
      apply (auto)[1]
      apply wp+
      apply (rule length_filter_take_np_2)
         apply simp
        apply simp
       apply simp
      apply simp
     apply (rule length_filter_le_2)
      apply simp
     apply (drule kdless_uint_length_true)
      apply simp
     apply simp
    (**If condition is true**)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: while_inv_def while_inv2_def)
         apply (simp add: while_inv_def while_inv2_def)
        apply (simp add: while_inv_def while_inv2_def)
       defer
       apply (simp add: while_inv_def while_inv2_def)
      apply (simp add: while_inv_def while_inv2_def)
     apply (simp add: while_inv_def while_inv2_def)
    apply wp
    apply wp
    apply wp
     defer
     apply (simp)
    apply (simp only:while_inv_def while_inv2_def)
    apply safe
    apply wp
    apply wp
    apply wp
      apply wp
      apply wp
     apply wp
     apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp)
         apply (simp)
        apply (simp)
       defer
       apply (simp)
      apply (simp)
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply wp
    apply wp
    apply wp
    apply (erule kdplus_safe_value_value)
    apply (simp)
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
          apply (simp)
         apply (simp)
        apply (simp)
       apply (simp)
      apply (simp)
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
          apply (simp add: wpsimps)
         apply (simp add: wpsimps)
        apply (simp add: wpsimps)
       defer
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     apply (simp add: wpsimps)
    apply wp
    apply wp
    apply wp
    apply wp
     defer
     apply wp
    apply wp
    apply wp
    apply (erule kdplus_safe_value_value)
    apply (simp)
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
          apply (simp add: wpsimps)
         apply (simp add: wpsimps)
        apply (simp add: wpsimps)
       apply (simp add: wpsimps)
      apply (simp add: wpsimps)
     defer
     apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (erule pred_someE)
    apply (erule pred_someE)
    apply (auto simp add: wpsimps while_inv_def while_inv2_def allItems_def mupdate_array_typing_value)[1]
          apply (simp add: mvalue_update_length)
         apply mc
         apply (simp add: wpsimps)
        apply (rule pred_some_read)
         apply mc+
          apply (simp)
         apply (simp)
        apply (drule kdless_uint_length_true,simp)
        apply (rule filter_items_prefix_suc_eq;simp)
       apply mc
        apply (simp)
       apply (simp)
      apply (rule pred_some_read)
       apply mc+
        apply (simp)
       apply (simp)
      apply (drule kdless_uint_length_true,simp)
      apply (rule updateCalldata_length)
            apply simp
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply (drule kdless_uint_length_true,simp)
     apply (simp add:nth_safe_def)
     apply (erule_tac P= "\<lambda>y. y < length daa \<longrightarrow> (\<exists>em. daa ! y = storage_data.Array em \<and> (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))" in allE)
     apply (auto)[1]
     apply (rule length_filter_take)
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    apply (drule kdless_uint_length_true,simp)
    apply wp+
    apply (simp add: unat_le_unat_suc)
    done
qed
end