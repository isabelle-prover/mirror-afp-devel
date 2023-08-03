theory Weakest_Precondition
  imports Solidity_Main
begin

section \<open>Setup for Monad VCG\<close>

lemma wpstackvalue[wprule]:
  assumes "\<And>v. a = KValue v \<Longrightarrow> wp (f v) P E s"
      and "\<And>p. a = KCDptr p \<Longrightarrow> wp (g p) P E s"
      and "\<And>p. a = KMemptr p \<Longrightarrow> wp (h p) P E s"
      and "\<And>p. a = KStoptr p \<Longrightarrow> wp (i p) P E s"
    shows "wp (case a of KValue v \<Rightarrow> f v | KCDptr p \<Rightarrow> g p | KMemptr p \<Rightarrow> h p | KStoptr p \<Rightarrow> i p) P E s"
using assms by (simp add: Stackvalue.split[of "\<lambda>x. wp x P E s"])

lemma wpmtypes[wprule]:
  assumes "\<And>i m. a = MTArray i m \<Longrightarrow> wp (f i m) P E s"
      and "\<And>t. a = MTValue t \<Longrightarrow> wp (g t) P E s"
    shows "wp (case a of MTArray i m \<Rightarrow> f i m | MTValue t \<Rightarrow> g t) P E s"
using assms by (simp add: MTypes.split[of "\<lambda>x. wp x P E s"])

lemma wpstypes[wprule]:
  assumes "\<And>i m. a = STArray i m \<Longrightarrow> wp (f i m) P E s"
      and "\<And>t t'. a = STMap t t' \<Longrightarrow> wp (g t t') P E s"
      and "\<And>t. a = STValue t \<Longrightarrow> wp (h t) P E s"
shows "wp (case a of STArray i m \<Rightarrow> f i m | STMap t t' \<Rightarrow> g t t' | STValue t \<Rightarrow> h t) P E s"
using assms by (simp add: STypes.split[of "\<lambda>x. wp x P E s"])

lemma wptype[wprule]:
  assumes "\<And>v. a = Value v \<Longrightarrow> wp (f v) P E s"
      and "\<And>m. a = Calldata m \<Longrightarrow> wp (g m) P E s"
      and "\<And>m. a = Memory m \<Longrightarrow> wp (h m) P E s"
      and "\<And>t. a = Storage t \<Longrightarrow> wp (i t) P E s"
shows "wp (case a of Value v \<Rightarrow> f v | Calldata m \<Rightarrow> g m | Memory m \<Rightarrow> h m | Storage s \<Rightarrow> i s) P E s"
  using assms by (simp add: Type.split[of "\<lambda>x. wp x P E s"])

lemma wptypes[wprule]:
assumes "\<And>x. a= TSInt x \<Longrightarrow> wp (f x) P E s"
    and "\<And>x. a = TUInt x \<Longrightarrow> wp (g x) P E s"
    and "a = TBool \<Longrightarrow> wp h P E s"
    and "a = TAddr \<Longrightarrow> wp i P E s"
  shows "wp (case a of TSInt x \<Rightarrow> f x | TUInt x \<Rightarrow> g x | TBool \<Rightarrow> h | TAddr \<Rightarrow> i) P E s"
using assms by (simp add: Types.split[of "\<lambda>x. wp x P E s"])

lemma wpltype[wprule]:
  assumes "\<And>l. a=LStackloc l \<Longrightarrow> wp (f l) P E s"
      and "\<And>l. a = LMemloc l \<Longrightarrow> wp (g l) P E s"
      and "\<And>l. a = LStoreloc l \<Longrightarrow> wp (h l) P E s"
    shows "wp (case a of LStackloc l \<Rightarrow> f l | LMemloc l \<Rightarrow> g l | LStoreloc l \<Rightarrow> h l) P E s"
using assms by (simp add: LType.split[of "\<lambda>x. wp x P E s"])

lemma wpdenvalue[wprule]:
  assumes "\<And>l. a=Stackloc l \<Longrightarrow> wp (f l) P E s"
      and "\<And>l. a=Storeloc l \<Longrightarrow> wp (g l) P E s"
    shows "wp (case a of Stackloc l \<Rightarrow> f l | Storeloc l \<Rightarrow> g l) P E s"
  using assms by (simp add:Denvalue.split[of "\<lambda>x. wp x P E s" f g a])

section \<open>Calculus\<close>

subsection \<open>Hoare Triples\<close>

type_synonym State_Predicate = "Accounts \<times> Stack \<times> MemoryT \<times> (Address \<Rightarrow> StorageT) \<Rightarrow> bool"

definition validS :: "State_Predicate \<Rightarrow> (unit, Ex ,State) state_monad \<Rightarrow> State_Predicate \<Rightarrow> (Ex \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>\<^sub>S/ _ /(\<lbrace>_\<rbrace>\<^sub>S,/ \<lbrace>_\<rbrace>\<^sub>S)")
where
  "\<lbrace>P\<rbrace>\<^sub>S f \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S \<equiv>
     \<forall>st. P (accounts st, stack st, memory st, storage st)
     \<longrightarrow> (case f st of
           Normal (_,st') \<Rightarrow> gas st' \<le> gas st \<and> Q (accounts st', stack st', memory st', storage st')
         | Exception e \<Rightarrow> E e)"

definition wpS :: "(unit, Ex ,State) state_monad \<Rightarrow> (State \<Rightarrow> bool) \<Rightarrow> (Ex \<Rightarrow> bool) \<Rightarrow> State \<Rightarrow> bool"
  where "wpS f P E st \<equiv> wp f (\<lambda>_ st'. gas st' \<le> gas st \<and> P st') E st"

lemma wpS_valid:
  assumes "\<And>st::State. P (accounts st, stack st, memory st, storage st) \<Longrightarrow> wpS f (\<lambda>st. Q (accounts st, stack st, memory st, storage st)) E st"
  shows "\<lbrace>P\<rbrace>\<^sub>S f \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S"
  unfolding validS_def
  using assms unfolding wpS_def wp_def by simp

lemma valid_wpS:
  assumes "\<lbrace>P\<rbrace>\<^sub>S f \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S"
  shows "\<And>st. P (accounts st, stack st, memory st, storage st) \<Longrightarrow> wpS f (\<lambda>st. Q (accounts st, stack st, memory st, storage st))E st"
  unfolding wpS_def wp_def using assms unfolding validS_def by simp

context statement_with_gas
begin

subsection \<open>Skip\<close>

lemma wp_Skip:
  assumes "P (st\<lparr>gas := gas st - costs SKIP ev cd st\<rparr>)"
      and "E Gas"
    shows "wpS (\<lambda>s. stmt SKIP ev cd s) P E st"
  apply (subst stmt.simps(1))
  unfolding wpS_def
  apply wp
  using assms by auto

subsection \<open>Assign\<close>

lemma wp_Assign:
  fixes ex ev cd st lv
  defines "ngas \<equiv> gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>v t g l t' g' v'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KValue v, Value t), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Value t'), g');
             g' \<le> gas st;
             convert t t' v = Some v'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', stack:=updateStore l (KValue v') (stack st)\<rparr>)"
      and "\<And>v t g l t' g' v'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KValue v, Value t), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, Storage (STValue t')), g');
             g' \<le> gas st;
             convert t t' v = Some v'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := (fmupd l v' (storage st (address ev))))\<rparr>)"
      and "\<And>v t g l t' g' v' vt.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KValue v, Value t), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, Memory (MTValue t')), g');
             g' \<le> gas st;
             convert t t' v = Some v'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=updateStore l (MValue v') (memory st)\<rparr>)"
      and "\<And>p x t g l t' g' p' m'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory t'), g');
             g' \<le> gas st;
             accessStore l (stack st) = Some (KMemptr p');
             cpm2m p p' x t cd (memory st) = Some m'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=m'\<rparr>)"
      and "\<And>p x t g l t' g' p' s'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage t'), g');
             g' \<le> gas st;
             accessStore l (stack st) = Some (KStoptr p');
             cpm2s p p' x t cd (storage st (address ev)) = Some s'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := s')\<rparr>)"
      and "\<And>p x t g l t' g' s'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
             g' \<le> gas st;
             cpm2s p l x t cd (storage st (address ev)) = Some s'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := s')\<rparr>)"
      and "\<And>p x t g l t' g' m'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, t'), g');
             g' \<le> gas st;
             cpm2m p l x t cd (memory st) = Some m'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=m'\<rparr>)"
      and "\<And>p x t g l t' g'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KMemptr p, Memory (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory t'), g');
             g' \<le> gas st\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', stack:=updateStore l (KMemptr p) (stack st)\<rparr>)"
      and "\<And>p x t g l t' g' p' s'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KMemptr p, Memory (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage t'), g');
             g' \<le> gas st;
             accessStore l (stack st) = Some (KStoptr p');
             cpm2s p p' x t (memory st) (storage st (address ev)) = Some s'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := s')\<rparr>)"
      and "\<And>p x t g l t' g' s'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KMemptr p, Memory (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
             g' \<le> gas st;
             cpm2s p l x t (memory st) (storage st (address ev)) = Some s'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := s')\<rparr>)"
      and "\<And>p x t g l t' g'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KMemptr p, Memory (MTArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, t'), g');
             g' \<le> gas st\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=updateStore l (MPointer p) (memory st)\<rparr>)"
      and "\<And>p x t g l t' g' p' m'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KStoptr p, Storage (STArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory t'), g');
             g' \<le> gas st;
             accessStore l (stack st) = Some (KMemptr p');
             cps2m p p' x t (storage st (address ev)) (memory st) = Some m'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=m'\<rparr>)"
      and "\<And>p x t g l t' g'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KStoptr p, Storage (STArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage t'), g');
             g' \<le> gas st\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', stack:=updateStore l (KStoptr p) (stack st)\<rparr>)"
      and "\<And>p x t g l t' g' s'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KStoptr p, Storage (STArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
             g' \<le> gas st;
             copy p l x t (storage st (address ev)) = Some s'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', storage:=(storage st) (address ev := s')\<rparr>)"
      and "\<And>p x t g l t' g' m'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KStoptr p, Storage (STArray x t)), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, t'), g');
             g' \<le> gas st;
             cps2m p l x t (storage st (address ev)) (memory st) = Some m'\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', memory:=m'\<rparr>)"
      and "\<And>p t t' g l t'' g'.
             \<lbrakk>expr ex ev cd (st\<lparr>gas := ngas\<rparr>) ngas = Normal ((KStoptr p, Storage (STMap t t')), g);
             lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, t''), g');
             g' \<le> gas st\<rbrakk>
           \<Longrightarrow> P (st\<lparr>gas := g', stack:=updateStore l (KStoptr p) (stack st)\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (\<lambda>s. stmt (ASSIGN lv ex) ev cd s) P E st"
  apply (subst stmt.simps(2))
  unfolding wpS_def
  apply wp
  apply (simp_all add: Ex.induct[OF assms(18,19)])
proof -
  fix a g aa b v t ab ga ac ba l t' v'
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
     and "a = (KValue v, Value t)"
     and "aa = KValue v"
     and "b = Value t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Value t'), ga)"
     and "ab = (LStackloc l, Value t')"
     and "ac = LStackloc l"
     and "ba = Value t'"
     and "convert t t' v = Some v'"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, stack := updateStore l (KValue v') (stack st)\<rparr>)" using assms(2) unfolding ngas_def by simp
next
  fix a g aa b v t ab ga ac ba l MTypes t' v'
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
     and "a = (KValue v, Value t)"
     and "aa = KValue v"
     and "b = Value t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, Memory (MTValue t')), ga)"
     and "ab = (LMemloc l, Memory (MTValue t'))"
     and "ac = LMemloc l"
     and "ba = Memory (MTValue t')"
     and "MTypes = MTValue t'"
     and "convert t t' v = Some v'"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := updateStore l (MValue v') (memory st)\<rparr>)" using assms(4) unfolding ngas_def by simp
next
  fix a g aa b v t ab ga ac ba l ta Types v'
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
     and "a = (KValue v, Value t)"
     and "aa = KValue v"
     and "b = Value t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, Storage (STValue Types)), ga)"
     and "ab = (LStoreloc l, Storage (STValue Types))"
     and "ac = LStoreloc l"
     and "ba = Storage (STValue Types)"
     and "ta = STValue Types"
     and "convert t Types v = Some v'"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := fmupd l v' (storage st (address ev)))\<rparr>)" using assms(3) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l MTypesa y literal ya
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
     and "a = (KCDptr p, Calldata (MTArray x t))"
     and "aa = KCDptr p"
     and "b = Calldata (MTArray x t)"
     and "MTypes = MTArray x t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory MTypesa), ga)"
     and "ab = (LStackloc l, Memory MTypesa)"
     and "ac = LStackloc l"
     and "xa = Memory MTypesa"
     and "accessStore l (stack st) = Some (KMemptr literal)"
     and "y = KMemptr literal"
     and "cpm2m p literal x t cd (memory st) = Some ya"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := ya\<rparr>)" using assms(5) unfolding ngas_def by simp
next
     fix a g aa b p MTypes x t ab ga ac xa l ta y literal ya
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
     and "a = (KCDptr p, Calldata (MTArray x t))"
     and "aa = KCDptr p"
     and "b = Calldata (MTArray x t)"
     and "MTypes = MTArray x t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage ta), ga)"
     and "ab = (LStackloc l, Storage ta)"
     and "ac = LStackloc l"
     and "xa = Storage ta"
     and "accessStore l (stack st) = Some (KStoptr literal)"
     and "y = KStoptr literal"
     and "cpm2s p literal x t cd (storage st (address ev)) = Some ya"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := ya)\<rparr>)" using assms(6) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l y
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
     and "a = (KCDptr p, Calldata (MTArray x t))"
     and "aa = KCDptr p"
     and "b = Calldata (MTArray x t)"
     and "MTypes = MTArray x t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, xa), ga)"
     and "ab = (LMemloc l, xa)"
     and "ac = LMemloc l"
     and "cpm2m p l x t cd (memory st) = Some y"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := y\<rparr>)" using assms(8) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l y
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
     and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
     and "a = (KCDptr p, Calldata (MTArray x t))"
     and "aa = KCDptr p"
     and "b = Calldata (MTArray x t)"
     and "MTypes = MTArray x t"
     and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, xa), ga)"
     and "ab = (LStoreloc l, xa)"
     and "ac = LStoreloc l"
     and "cpm2s p l x t cd (storage st (address ev)) = Some y"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := y)\<rparr>)" using assms(7) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l MTypesa
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
    and "a = (KMemptr p, Memory (MTArray x t))"
    and "aa = KMemptr p"
    and "b = Memory (MTArray x t)"
    and "MTypes = MTArray x t"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory MTypesa), ga)"
    and "ab = (LStackloc l, Memory MTypesa)"
    and "ac = LStackloc l"
    and "xa = Memory MTypesa"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, stack := updateStore l (KMemptr p) (stack st)\<rparr>)" using assms(9) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l ta y literal ya
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
    and "a = (KMemptr p, Memory (MTArray x t))"
    and "aa = KMemptr p"
    and "b = Memory (MTArray x t)"
    and "MTypes = MTArray x t"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage ta), ga)"
    and "ab = (LStackloc l, Storage ta)"
    and "ac = LStackloc l"
    and "xa = Storage ta"
    and "accessStore l (stack st) = Some (KStoptr literal)"
    and "y = KStoptr literal"
    and "cpm2s p literal x t (memory st) (storage st (address ev)) = Some ya"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := ya)\<rparr>)" using assms(10) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
    and "a = (KMemptr p, Memory (MTArray x t))"
    and "aa = KMemptr p"
    and "b = Memory (MTArray x t)"
    and "MTypes = MTArray x t"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, xa), ga)"
    and "ab = (LMemloc l, xa)"
    and "ac = LMemloc l"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := updateStore l (MPointer p) (memory st)\<rparr>)" using assms(12) unfolding ngas_def by simp
next
  fix a g aa b p MTypes x t ab ga ac xa l y
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
    and "a = (KMemptr p, Memory (MTArray x t))"
    and "aa = KMemptr p"
    and "b = Memory (MTArray x t)"
    and "MTypes = MTArray x t"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, xa), ga)"
    and "ab = (LStoreloc l, xa)"
    and "ac = LStoreloc l"
    and "cpm2s p l x t (memory st) (storage st (address ev)) = Some y"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := y)\<rparr>)" using assms(11) unfolding ngas_def by simp
next
  fix a g aa b p t x ta ab ga ac xa l MTypes y literal ya
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x ta)), g)"
    and "a = (KStoptr p, Storage (STArray x ta))"
    and "aa = KStoptr p"
    and "b = Storage (STArray x ta)"
    and "t = STArray x ta"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Memory MTypes), ga)"
    and "ab = (LStackloc l, Memory MTypes)"
    and "ac = LStackloc l"
    and "xa = Memory MTypes"
    and "accessStore l (stack st) = Some (KMemptr literal)"
    and "y = KMemptr literal"
    and "cps2m p literal x ta (storage st (address ev)) (memory st) = Some ya"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := ya\<rparr>)" using assms(13) unfolding ngas_def by simp
next
 fix a g aa b p t x ta ab ga ac xa l tb
 assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x ta)), g)"
    and "a = (KStoptr p, Storage (STArray x ta))"
    and "aa = KStoptr p"
    and "b = Storage (STArray x ta)"
    and "t = STArray x ta"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, Storage tb), ga)"
    and "ab = (LStackloc l, Storage tb)"
    and "ac = LStackloc l"
    and "xa = Storage tb"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, stack := updateStore l (KStoptr p) (stack st)\<rparr>)" using assms(14) unfolding ngas_def by simp
next
 fix a g aa b p t x ta ab ga ac xa l y
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x ta)), g)"
    and "a = (KStoptr p, Storage (STArray x ta))"
    and "aa = KStoptr p"
    and "b = Storage (STArray x ta)"
    and "t = STArray x ta"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LMemloc l, xa), ga)"
    and "ab = (LMemloc l, xa)"
    and "ac = LMemloc l"
    and "cps2m p l x ta (storage st (address ev)) (memory st) = Some y"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, memory := y\<rparr>)" using assms(16) unfolding ngas_def by simp
next
 fix a g aa b p t x ta ab ga ac xa l y
  assume "costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x ta)), g)"
    and "a = (KStoptr p, Storage (STArray x ta))"
    and "aa = KStoptr p"
    and "b = Storage (STArray x ta)"
    and "t = STArray x ta"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l, xa), ga)"
    and "ab = (LStoreloc l, xa)"
    and "ac = LStoreloc l"
    and "copy p l x ta (storage st (address ev)) = Some y"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, storage := (storage st) (address ev := y)\<rparr>)" using assms(15) unfolding ngas_def by simp
next
 fix a g aa b p t ta t' ab ga ac x l
  assume "   costs (ASSIGN lv ex) ev cd st < gas st"
    and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STMap ta t')), g)"
    and "a = (KStoptr p, Storage (STMap ta t'))"
    and "aa = KStoptr p"
    and "b = Storage (STMap ta t')"
    and "t = STMap ta t'"
    and **: "local.lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, x), ga)"
    and "ab = (LStackloc l, x)"
    and "ac = LStackloc l"
  moreover have "ga \<le> gas st"
  proof -
    have "ga \<le> g" using lexp_gas[OF **] by simp
    also have "\<dots> \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    finally show ?thesis .
  qed
  ultimately show "ga \<le> gas st \<and> P (st\<lparr>gas := ga, stack := updateStore l (KStoptr p) (stack st)\<rparr>)" using assms(17) unfolding ngas_def by simp
qed

subsection \<open>Composition\<close>

lemma wp_Comp:
  assumes "wpS (stmt s1 ev cd) (\<lambda>st. wpS (stmt s2 ev cd) P E st) E (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (\<lambda>s. stmt (COMP s1 s2) ev cd s) P E st"
  apply (subst stmt.simps(3))
  unfolding wpS_def
  apply wp
  using assms unfolding wpS_def wp_def by (auto split:result.split)

subsection \<open>Conditional\<close>

lemma wp_ITE:
  assumes "\<And>g g'. expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue \<lceil>True\<rceil>, Value TBool), g') \<Longrightarrow> wpS (stmt s1 ev cd) P E (st\<lparr>gas := g'\<rparr>)"
      and "\<And>g g'. expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue \<lceil>False\<rceil>, Value TBool), g') \<Longrightarrow> wpS (stmt s2 ev cd) P E (st\<lparr>gas := g'\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (\<lambda>s. stmt (ITE ex s1 s2) ev cd s) P E st"
  apply (subst stmt.simps(4))
  unfolding wpS_def
  apply wp
  apply (simp_all add: Ex.induct[OF assms(3,4)])
  proof -
    fix a g aa ba b v
    assume "costs (ITE ex s1 s2) ev cd st < gas st"
       and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ITE ex s1 s2) ev cd st\<rparr>) (gas st - costs (ITE ex s1 s2) ev cd st) = Normal ((KValue \<lceil>True\<rceil>, Value TBool), g)"
       and "a = (KValue \<lceil>True\<rceil>, Value TBool)"
       and "aa = KValue \<lceil>True\<rceil>" and "ba = Value TBool" and "v = TBool" and "b = \<lceil>True\<rceil>"
    then have "wpS (stmt s1 ev cd) P E (st\<lparr>gas := g\<rparr>)" using assms(1) by simp
    moreover have "g \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    ultimately show "wp (local.stmt s1 ev cd) (\<lambda>_ st'. gas st' \<le> gas st \<and> P st') E (st\<lparr>gas := g\<rparr>)"
      unfolding wpS_def wp_def by (simp split:result.split_asm prod.split_asm)
  next
    fix a g aa ba b v
    assume "costs (ITE ex s1 s2) ev cd st < gas st"
       and *: "local.expr ex ev cd (st\<lparr>gas := gas st - costs (ITE ex s1 s2) ev cd st\<rparr>) (gas st - costs (ITE ex s1 s2) ev cd st) = Normal ((KValue \<lceil>False\<rceil>, Value TBool), g)"
       and "a = (KValue \<lceil>False\<rceil>, Value TBool)"
       and "aa = KValue \<lceil>False\<rceil>" and "ba = Value TBool" and "v = TBool" and "b = \<lceil>False\<rceil>"
    then have "wpS (stmt s2 ev cd) P E (st\<lparr>gas := g\<rparr>)" using assms(2) by simp
    moreover have "g \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF *] by simp
    ultimately show "wp (local.stmt s2 ev cd) (\<lambda>_ st'. gas st' \<le> gas st \<and> P st') E (st\<lparr>gas := g\<rparr>)"
      unfolding wpS_def wp_def by (simp split:result.split_asm prod.split_asm)
  qed

subsection \<open>While Loop\<close>

lemma wp_While[rule_format]:
    fixes iv::"Accounts \<times> Stack \<times> MemoryT \<times> (Address \<Rightarrow> StorageT) \<Rightarrow> bool"
  assumes "\<And>a k m s st g. \<lbrakk>iv (a, k, m, s); expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex sm) ev cd st\<rparr>) (gas st - costs (WHILE ex sm) ev cd st) = Normal ((KValue \<lceil>False\<rceil>, Value TBool), g)\<rbrakk> \<Longrightarrow> P (st\<lparr>gas := g\<rparr>)"
      and "\<And>a k m s st g. \<lbrakk>iv (a, k, m, s); expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex sm) ev cd st\<rparr>) (gas st - costs (WHILE ex sm) ev cd st) = Normal ((KValue \<lceil>True\<rceil>, Value TBool), g)\<rbrakk> \<Longrightarrow> wpS (stmt sm ev cd) (\<lambda>st. iv (accounts st, stack st, memory st, storage st)) E (st\<lparr>gas:=g\<rparr>)"
      and "E Err"
      and "E Gas"
    shows "iv (accounts st, stack st, memory st, storage st) \<longrightarrow> wpS (\<lambda>s. stmt (WHILE ex sm) ev cd s) P E st"
proof (induction st rule:gas_induct)
  case (1 st)
  show ?case
  unfolding wpS_def wp_def
  proof (split result.split, rule conjI; rule allI; rule impI)
    fix x1 assume *: "local.stmt (WHILE ex sm) ev cd st = Normal x1"
    then obtain b g where **: "expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex sm) ev cd st\<rparr>) (gas st - costs (WHILE ex sm) ev cd st) = Normal ((KValue b, Value TBool), g)" by (simp only: stmt.simps, simp split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
    with * consider (t) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True" | (f) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" by (simp add:stmt.simps split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
    then show "iv (accounts st, stack st, memory st, storage st) \<longrightarrow> (case x1 of (r, s') \<Rightarrow> gas s' \<le> gas st \<and> P s')"
    proof cases
      case t
      then obtain st' where ***: "stmt sm ev cd (st\<lparr>gas := g\<rparr>) = Normal ((), st')" using * ** by (auto simp add:stmt.simps split:if_split_asm result.split_asm)
      then have ****: "local.stmt (WHILE ex sm) ev cd st' = Normal x1" using * ** t by (simp add:stmt.simps split:if_split_asm)
      show ?thesis
      proof
        assume "iv (accounts st, stack st, memory st, storage st)"
        then have "wpS (local.stmt sm ev cd) (\<lambda>st. iv (accounts st, stack st, memory st, storage st)) E (st\<lparr>gas:=g\<rparr>)" using assms(2) ** t by auto
        then have "iv (accounts st', stack st', memory st', storage st')" unfolding wpS_def wp_def using *** by (simp split:result.split_asm)+
        moreover have "gas st \<ge> costs (WHILE ex sm) ev cd st" using * by (simp add:stmt.simps split:if_split_asm)
        then have "gas st' < gas st" using stmt_gas[OF ***] msel_ssel_expr_load_rexp_gas(3)[OF **] while_not_zero[of ex sm ev cd st] by simp
        ultimately have "wpS (local.stmt (WHILE ex sm) ev cd) P E st'" using 1 by simp
        then show "(case x1 of (r, s') \<Rightarrow> gas s' \<le> gas st \<and> P s')" unfolding wpS_def wp_def using **** `gas st' < gas st` by auto
      qed
    next
      case f
      show ?thesis
      proof
        assume "iv (accounts st, stack st, memory st, storage st)"
        then have "P (st\<lparr>gas := g\<rparr>)" using ** assms(1) f by simp
        moreover have "x1 = ((),st\<lparr>gas := g\<rparr>)" using * ** f by (simp add:stmt.simps true_neq_false[symmetric] split:if_split_asm)
        moreover have "g \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF **] by simp
        ultimately show "case x1 of (r, s') \<Rightarrow> gas s' \<le> gas st \<and> P s'" by (auto split:prod.split)
      qed
    qed
  next
    fix x2
    show "iv (accounts st, stack st, memory st, storage st) \<longrightarrow> E x2" using assms(3,4) Ex.nchotomy by metis
  qed
qed

subsection \<open>Blocks\<close>

lemma wp_blockNone:
  assumes "\<And>cd' mem' sck' e'. decl id0 tp None False cd (memory (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) stm) ev cd st\<rparr>)) (storage (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) stm) ev cd st\<rparr>))
           (cd, memory (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) stm) ev cd st\<rparr>), stack (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) stm) ev cd st\<rparr>), ev) = Some (cd', mem', sck', e')
          \<Longrightarrow> wpS (stmt stm e' cd') P E (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) stm) ev cd st, stack := sck', memory := mem'\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (\<lambda>s. stmt (BLOCK ((id0, tp), None) stm) ev cd s) P E st"
  unfolding wpS_def wp_def
proof ((split result.split | split prod.split)+, rule conjI; (rule allI | rule impI)+)
  fix x1 x1a x2
  assume "x1 = (x1a, x2)"
    and "local.stmt (BLOCK ((id0, tp), None) stm) ev cd st = Normal x1"
  then have "local.stmt (BLOCK ((id0, tp), None) stm) ev cd st = Normal (x1a, x2)" by simp
  then show "gas x2 \<le> gas st \<and> P x2"
  proof (cases rule: blockNone)
    case (1 cd' mem' sck' e')
    then show ?thesis using assms(1)[OF 1(2)] unfolding wpS_def wp_def by auto
  qed
next
  fix e
  assume "local.stmt (BLOCK ((id0, tp), None) stm) ev cd st = Exception e"
  show "E e" using assms(2,3) by (induction rule: Ex.induct)
qed

lemma wp_blockSome:
  assumes "\<And>v t g' cd' mem' sck' e'.
        \<lbrakk> expr ex' ev cd (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), Some ex') stm) ev cd st\<rparr>) (gas st - costs (BLOCK ((id0, tp), Some ex') stm) ev cd st) = Normal ((v, t), g');
          g' \<le> gas st - costs (BLOCK ((id0, tp), Some ex') stm) ev cd st;
          decl id0 tp (Some (v,t)) False cd (memory st) (storage st) (cd, memory st, stack st, ev) = Some (cd', mem', sck', e')\<rbrakk>
        \<Longrightarrow> wpS (stmt stm e' cd') P E (st\<lparr>gas := g', stack := sck', memory := mem'\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (\<lambda>s. stmt (BLOCK ((id0, tp), Some ex') stm) ev cd s) P E st"
  unfolding wpS_def wp_def
proof ((split result.split | split prod.split)+, rule conjI; (rule allI | rule impI)+)
  fix x1 x1a x2
  assume "x1 = (x1a, x2)"
    and "local.stmt (BLOCK ((id0, tp), Some ex') stm) ev cd st = Normal x1"
  then have "local.stmt (BLOCK ((id0, tp), Some ex') stm) ev cd st = Normal (x1a, x2)" by simp
  then show "gas x2 \<le> gas st \<and> P x2"
  proof (cases rule: blockSome)
    case (1 v t g cd' mem' sck' e')
    moreover have "g \<le> gas st - costs (BLOCK ((id0, tp), Some ex') stm) ev cd st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
    ultimately show ?thesis using assms(1)[OF 1(2)] unfolding wpS_def wp_def by auto
  qed
next
  fix e
  assume "local.stmt (BLOCK ((id0, tp), Some ex') stm) ev cd st = Exception e"
  show "E e" using assms(2,3) by (induction rule: Ex.induct)
qed

end

subsection \<open>External method invocation\<close>

locale Calculus = statement_with_gas +
  fixes cname::Identifier
    and members:: "(Identifier, Member) fmap"
    and const::"(Identifier \<times> Type) list \<times> S"
    and fb :: S
assumes C1: "ep $$ cname = Some (members, const, fb)"
begin

text \<open>
  The rules for method invocations is provided in the context of four parameters:
  \<^item> @{term_type cname}: The name of the contract to be verified
  \<^item> @{term_type members}: The member variables of the contract to be verified
  \<^item> @{term const}: The constructor of the contract to be verified
  \<^item> @{term fb}: The fallback method of the contract to be verified

In addition @{thm[source] C1} assigns members, constructor, and fallback method to the contract address.
\<close>

text \<open>
  An invariant is a predicate over two parameters:
  \<^item> The private store of the contract
  \<^item> The balance of the contract
\<close>

type_synonym Invariant = "StorageT \<Rightarrow> int \<Rightarrow> bool"

subsection \<open>Method invocations and transfer\<close>

definition Qe
  where "Qe ad iv st \<equiv>
    (\<forall>mid fp f ev.
       members $$ mid = Some (Method (fp,True,f)) \<and>
       address ev \<noteq> ad
      \<longrightarrow> (\<forall>adex cd st' xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc.
            g'' \<le> gas st \<and>
            type (acc ad) = Some (Contract cname) \<and>
            expr adex ev cd (st'\<lparr>gas := gas st' - costs (EXTERNAL adex mid xe val) ev cd st'\<rparr>) (gas st' - costs (EXTERNAL adex mid xe val) ev cd st') = Normal ((KValue ad, Value TAddr), g) \<and>
            expr val ev cd (st'\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
            convert t (TUInt 256) v = Some v' \<and>
            load True fp xe (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore emptyStore emptyStore ev cd (st'\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'') \<and>
            transfer (address ev) ad v' (accounts (st'\<lparr>gas := g''\<rparr>)) = Some acc \<and>
            iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
           \<longrightarrow> wpS (stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st'\<lparr>gas := g'', accounts:= acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)))"

definition Qi
  where "Qi ad pre post st \<equiv>
   (\<forall>mid fp f ev.
     members $$ mid = Some (Method (fp,False,f)) \<and>
     address ev = ad
    \<longrightarrow> (\<forall>cd st' i xe e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
          g \<le> gas st \<and>
          load False fp xe (ffold (init members) (emptyEnv ad cname (sender ev) (svalue ev)) (fmdom members)) emptyStore emptyStore (memory st') ev cd (st'\<lparr>gas := gas st' - costs (INVOKE i xe) ev cd st'\<rparr>) (gas st' - costs (INVOKE i xe) ev cd st') = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g) \<and>
          pre mid (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)), storage st' ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)
         \<longrightarrow> wpS (stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. post mid (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) (st'\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)))"

definition Qfi
  where "Qfi ad pref postf st \<equiv>
   (\<forall>ev. address ev = ad
    \<longrightarrow> (\<forall>ex cd st' adex cc v t g g' v' acc.
          g' \<le> gas st \<and>
          expr adex ev cd (st'\<lparr>gas := gas st' - cc\<rparr>) (gas st' - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
          expr ex ev cd (st'\<lparr>gas := g\<rparr>) g= Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt 256) v = Some v' \<and>
          transfer (address ev) ad v' (accounts st') = Some acc \<and>
          pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)), storage st' ad)
         \<longrightarrow> wpS (\<lambda>s. stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore s) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) (st'\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)))"

definition Qfe
  where "Qfe ad iv st \<equiv>
   (\<forall>ev. address ev \<noteq> ad
    \<longrightarrow> (\<forall>ex cd st' adex cc v t g g' v' acc.
          g' \<le> gas st \<and>
          type (acc ad) = Some (Contract cname) \<and>
          expr adex ev cd (st'\<lparr>gas := gas st' - cc\<rparr>) (gas st' - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
          expr ex ev cd (st'\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt 256) v = Some v' \<and>
          transfer (address ev) ad v' (accounts st') = Some acc \<and>
          iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
         \<longrightarrow> wpS (\<lambda>s. stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore s) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st'\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)))"

lemma safeStore[rule_format]:
  fixes ad iv
  defines "aux1 st \<equiv> \<forall>st'::State. gas st' < gas st \<longrightarrow> Qe ad iv st'"
      and "aux2 st \<equiv> \<forall>st'::State. gas st' < gas st \<longrightarrow> Qfe ad iv st'"
    shows "\<forall>st'. address ev \<noteq> ad \<and> type (accounts st ad) = Some (Contract cname) \<and> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad))) \<and>
            stmt f ev cd st = Normal ((), st') \<and> aux1 st \<and> aux2 st
           \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
proof (induction rule:stmt.induct[where ?P="\<lambda>f ev cd st. \<forall>st'. address ev \<noteq> ad \<and> type (accounts st ad) = Some (Contract cname) \<and> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad))) \<and> stmt f ev cd st = Normal ((), st') \<and> aux1 st \<and> aux2 st \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"])
  case (1 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and *: "local.stmt SKIP ev cd st = Normal ((), st')"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using skip[OF *] by simp
  qed
next
  case (2 lv ex ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume "address ev \<noteq> ad" and "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and 3: "stmt (ASSIGN lv ex) ev cd st = Normal ((), st')"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" by (cases rule: assign[OF 3]; simp)
  qed
next
  case (3 s1 s2 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (COMP s1 s2) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof  (cases rule: comp[OF l3])
      case (1 st'')
      moreover have *:"assert Gas (\<lambda>st. costs (COMP s1 s2) ev cd st < gas st) st = Normal ((), st)" using l3 by (simp add:stmt.simps split:if_split_asm)
      moreover from l2 have "iv (storage (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad)))" by simp
      moreover have **:"gas (st\<lparr>gas:= gas st - costs (COMP s1 s2) ev cd st\<rparr>) \<le> gas st" by simp
      then have "aux1 (st\<lparr>gas:= gas st - costs (COMP s1 s2) ev cd st\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= gas st - costs (COMP s1 s2) ev cd st\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using 3(1) C1 l1 l12 by auto
      moreover from l12 have "type (accounts st'' ad) = Some (Contract cname)" using atype_same[OF 1(2), of ad "Contract cname"] l12 by auto
      moreover have **:"gas st'' \<le> gas st" using stmt_gas[OF 1(2)] by simp
      then have "aux1 st''" using 4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 st''" using 5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 3(2)[OF * _ 1(2), of "()"] 1(3) C1 l1 by simp
    qed
  qed
next
  case (4 ex s1 s2 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (ITE ex s1 s2) ev cd st = Normal ((), st')" and l4:"aux1 st" and l5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof (cases rule: ite[OF l3])
      case (1 g)
      moreover from l2 have "iv (storage (st\<lparr>gas :=g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g\<rparr>) ad)))" by simp
      moreover from l12 have "type (accounts (st\<lparr>gas:= g\<rparr>) ad) = Some (Contract cname)" using atype_same[OF 1(3), of ad "Contract cname"] l12 by auto
      moreover have **:"gas (st\<lparr>gas:= g\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 4(1) l1 by simp
    next
      case (2 g)
      moreover from l2 have "iv (storage (st\<lparr>gas := g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g\<rparr>) ad)))" by simp
      moreover from l12 have "type (accounts (st\<lparr>gas:= g\<rparr>) ad) = Some (Contract cname)" using atype_same[OF 2(3), of ad "Contract cname"] l12 by auto
      moreover have **:"gas (st\<lparr>gas:= g\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] by simp
      then have "aux1 (st\<lparr>gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 4(2) l1 true_neq_false by simp
    qed
  qed
next
  case (5 ex s0 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (WHILE ex s0) ev cd st = Normal ((), st')" and l4:"aux1 st" and l5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof (cases rule: while[OF l3])
      case (1 g st'')
      moreover from l2 have "iv (storage (st\<lparr>gas :=g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g\<rparr>) ad)))" by simp
      moreover have *:"gas (st\<lparr>gas:= g\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using 5(1) l1 l12 by simp
      moreover from l12 have "type (accounts st'' ad) = Some (Contract cname)" using atype_same[OF 1(3), of ad "Contract cname"] l12 by auto
      moreover have **:"gas st'' \<le> gas st" using stmt_gas[OF 1(3)] * by simp
      then have "aux1 st''" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 st''" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 5(2) 1(1,2,3,4) l1 by simp
    next
      case (2 g)
      then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using l2 by simp
    qed
  qed
next
  case (6 i xe ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume 1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and 2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and 3: "local.stmt (INVOKE i xe) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    from 3 obtain ct fb' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st''
      where l0: "costs (INVOKE i xe) ev cd st < gas st"
      and l1: "ep $$ contract ev = Some (ct, fb')"
      and l2: "ct $$ i = Some (Method (fp, False, f))"
      and l3: "load False fp xe (ffold (init ct) (emptyEnv (address ev) (contract ev) (sender ev) (svalue ev)) (fmdom ct)) emptyStore emptyStore (memory (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)"
      and l4: "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')"
      and l5: "st' = st''\<lparr>stack:=stack st\<rparr>"
      using invoke by blast
    from 3 have *:"assert Gas (\<lambda>st. costs (INVOKE i xe) ev cd st < gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
    moreover have **: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) st = Normal ((), st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)" by simp
    ultimately have "\<forall>st'. address e\<^sub>l \<noteq> ad \<and> iv (storage (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) ad))) \<and> local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<and> aux2 (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<longrightarrow>
      iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 6[OF * **] l1 l2 l3 l12 by (simp split:if_split_asm result.split_asm prod.split_asm option.split_asm)
    moreover have "address (ffold (init ct) (emptyEnv (address ev) (contract ev) (sender ev) (svalue ev)) (fmdom ct)) = address ev" using ffold_init_ad_same[of ct "(emptyEnv (address ev) (contract ev) (sender ev) (svalue ev))"] unfolding emptyEnv_def by simp
    with 1 have "address e\<^sub>l \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by simp
    moreover from 2 have "iv (storage (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) ad)))" by simp
    moreover have *:"gas (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by auto
    then have "aux1 (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
    moreover have *:"gas (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by auto
    then have "aux2 (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
    ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using l4 C1 by auto
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using l5  by simp
  qed
next
  case (7 ad' i xe val ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad"
      and l12:"type (accounts st ad) = Some (Contract cname)" 
      and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))"
      and 3: "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal ((), st')"
      and 4: "aux1 st" and 5:"aux2 st"
    show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof (cases rule: external[OF 3])
      case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover from this have "cname = c" using l12 1(4) by simp
        moreover from this have "members = ct" using C1 1(5) by simp
        moreover have "gas st \<ge>  costs (EXTERNAL ad' i xe val) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "g'' < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] external_not_zero[of ad' i xe val ev cd st] by auto
        then have "Qe ad iv (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using 4 unfolding aux1_def by simp
        moreover have "g'' \<le> gas (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" by simp
        moreover from l12 have "type (acc ad) = Some (Contract cname)" using transfer_type_same[OF 1(10)] by simp
        moreover have "i |\<in>| fmdom members" using 1(8) `members = ct` by (simp add: fmdomI)
        moreover have "members $$ i = Some (Method (fp,True,f))" using 1(8) `members = ct` by simp
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(10)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        ultimately have "wpS (local.stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" unfolding Qe_def using l1 l12 1(2) 1(6-10) by simp
        moreover have "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st'')" using 1(11) by simp
        ultimately show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" unfolding wpS_def wp_def using 1(12) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (EXTERNAL ad' i xe val) ev cd st < gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        moreover have **: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) st = Normal ((), st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>)" by simp
        ultimately have "\<forall>st'. address e\<^sub>l \<noteq> ad \<and> type (acc ad) = Some (Contract cname) \<and> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))) \<and> local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<and> aux2 (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 7(1)[OF * **] 1 by simp
        moreover have "address (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) = adv" using ffold_init_ad_same[of ct "(emptyEnv adv c (address ev) v)"] unfolding emptyEnv_def by simp
        with False have "address e\<^sub>l \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by simp
        moreover have "bal (acc ad) = bal ((accounts st) ad)" using transfer_eq[OF 1(10)] False l1 by simp
        then have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)))" using l2 by simp
        moreover have "type (acc ad) = Some (Contract cname)" using transfer_type_same l12 1(10) by simp
        moreover have *:"gas (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by auto
        then have "aux1 (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using 1(11) by simp
        then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 1(12) by simp
      qed
    next
      case (2 adv c g ct cn fb' v t g' v' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover have "gas st \<ge>  costs (EXTERNAL ad' i xe val) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] external_not_zero[of ad' i xe val ev cd st] by simp
        then have "Qfe ad iv (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 5 unfolding aux2_def by simp
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 2(9)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        moreover have "g' \<le> gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" by simp
        moreover from l12 have "type (acc ad) = Some (Contract cname)" using transfer_type_same[OF 2(9)] by simp
        ultimately have "wpS (local.stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" unfolding Qfe_def using l1 l12 2(2) 2(6-9) by blast
        moreover have "stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st'')"
        proof -
          from True have "cname = c" using l12 2(4) by simp
          moreover from this have "fb'=fb" using C1 2(5) by simp
          moreover from True `cname = c` have "members = ct" using C1 2(5) by simp
          ultimately show ?thesis using 2(10) True by simp
        qed
        ultimately show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" unfolding wpS_def wp_def using 2(11) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (EXTERNAL ad' i xe val) ev cd st < gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        then have "\<forall>st'. address (ffold (init ct) (emptyEnv adv c (address ev) v) (fmdom ct)) \<noteq> ad \<and>
          type (acc ad) = Some (Contract cname) \<and>
          iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))) \<and>
          local.stmt fb' (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) \<and> aux2 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)
          \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 7(2)[OF *] 2 by simp
        moreover from False have "address (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) \<noteq> ad" using ffold_init_ad_same[where ?e="\<lparr>address = adv, contract = c, sender = address ev, svalue = v, denvalue = {$$}\<rparr>" and ?e'="ffold (init ct) (emptyEnv adv c (address ev) v) (fmdom ct)"] unfolding emptyEnv_def by simp
        moreover have "bal (acc ad) = bal ((accounts st) ad)" using transfer_eq[OF 2(9)] False l1 by simp
        then have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)))"
          using l2 by simp
        moreover have "type (acc ad) = Some (Contract cname)" using transfer_type_same l12 2(9) by simp
        moreover have *:"gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] by simp
        then have "aux1 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using 2(10) by simp
        then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 2(11) by simp
      qed
    qed
  qed
next
  case (8 ad' ex ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and 3: "local.stmt (TRANSFER ad' ex) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof (cases rule: transfer[OF 3])
      case (1 v t g adv c g' v' acc ct cn f st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover have "gas st \<ge>  costs (TRANSFER ad' ex) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] transfer_not_zero[of ad' ex ev cd st] by auto
        then have "Qfe ad iv (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 5 unfolding aux2_def by simp
        moreover have "sender (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) \<noteq> ad" using l1 ffold_init_ad_same[where ?e = "(emptyEnv adv c (address ev) v')" and ?e'="ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)"] unfolding emptyEnv_def by simp
        moreover have "svalue (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) = v'" using ffold_init_ad_same[where ?e = "(emptyEnv adv c (address ev) v')" and ?e'="ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)", of ct "fmdom ct"] unfolding emptyEnv_def by simp
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(7)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        moreover have "g' \<le> gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" by simp
        moreover from l12 have "type (acc ad) = Some (Contract cname)" using transfer_type_same[OF 1(7)] by simp
        ultimately have "wpS (local.stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" unfolding Qfe_def using l1 l12 1(2-7) by blast
        moreover have "stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st'')"
        proof -
          from True have "cname = c" using l12 1(5) by simp
          moreover from this have "f=fb" using C1 1(6) by simp
          moreover from True `cname = c` have "members = ct" using C1 1(6) by simp
          ultimately show ?thesis using 1(8) True by simp
        qed
        ultimately show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" unfolding wpS_def wp_def using 1(9) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (TRANSFER ad' ex) ev cd st < gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        then have "\<forall>st'. address (ffold (init ct) (emptyEnv adv c (address ev) v) (fmdom ct)) \<noteq> ad \<and>
          type (acc ad) = Some (Contract cname) \<and>
          iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))) \<and>
          local.stmt f (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st') \<and>
          aux1 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) \<and> aux2 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)
          \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 8(1)[OF *] 1 by simp
        moreover from False have "address (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) \<noteq> ad" using ffold_init_ad_same[of ct "emptyEnv adv c (address ev) v"] unfolding emptyEnv_def by simp
        moreover have "bal (acc ad) = bal ((accounts st) ad)" using transfer_eq[OF 1(7)] False l1 by simp
        then have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)))"
          using l2 by simp
        moreover have "type (acc ad) = Some (Contract cname)" using transfer_type_same l12 1(7) by simp
        moreover have *:"gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] by simp
        then have "aux1 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st'' ad)))" using 1(8) C1 by simp
        then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 1(9) by simp
      qed
    next
      case (2 v t g adv g' v' acc)
      moreover from 2(5) have "adv \<noteq> ad" using C1 l12 by auto
      then have "bal (acc ad) = bal (accounts st ad)" using transfer_eq[OF 2(6)] l1 by simp
      ultimately show ?thesis using l2 by simp
    qed
  qed
next
  case (9 id0 tp s ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (BLOCK ((id0, tp), None) s) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof  (cases rule: blockNone[OF l3])
      case (1 cd' mem' sck' e')
      moreover from l2 have "iv (storage (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>) ad)))" by simp
      moreover have *:"gas (st\<lparr>gas:= gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>) \<le> gas st" by simp
      then have "aux1 (st\<lparr>gas:= gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      moreover have "address e' \<noteq> ad" using decl_env[OF 1(2)] l1 by simp
      ultimately show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 9(1) l12 by simp
    qed
  qed
next
  case (10 id0 tp ex' s ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (BLOCK ((id0, tp), Some ex') s) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof  (cases rule: blockSome[OF l3])
      case (1 v t g cd' mem' sck' e')
      moreover from l2 have "iv (storage (st\<lparr>gas := g, stack := sck', memory := mem'\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g, stack := sck', memory := mem'\<rparr>) ad)))" by simp
      moreover have *:"gas (st\<lparr>gas:= g, stack := sck', memory := mem'\<rparr>) \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>gas:= g, stack := sck', memory := mem'\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>gas:= g, stack := sck', memory := mem'\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      moreover have "address e' \<noteq> ad" using decl_env[OF 1(3)] l1 by simp
      ultimately show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))" using 10(1) l12 by simp
    qed
  qed
next
  case (11 i xe val ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "address ev \<noteq> ad" and l12:"type (accounts st ad) = Some (Contract cname)" and l2: "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" and l3: "stmt (NEW i xe val) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
    proof  (cases rule: new[OF l3])
      case (1 v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'')
      moreover define adv where "adv = hash (address ev) \<lfloor>contracts (accounts (st\<lparr>gas := gas st - costs (NEW i xe val) ev cd st\<rparr>) (address ev))\<rfloor>"
      moreover define st''' where "st''' = (st\<lparr>gas := gas st - costs (NEW i xe val) ev cd st, gas := g', accounts := (accounts st)(adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>), storage := (storage st)(adv := {$$}), accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)"
      ultimately have "\<forall>st'. address e\<^sub>l \<noteq> ad \<and>
        type (accounts st''' ad) = Some (Contract cname) \<and>
        iv (storage st''' ad) \<lceil>bal (accounts st''' ad)\<rceil> \<and>
        local.stmt (snd cn) e\<^sub>l cd\<^sub>l st''' = Normal ((), st') \<and> aux1 st''' \<and> aux2 st''' \<longrightarrow>
        iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        using 11 by simp
      moreover have "address e\<^sub>l \<noteq> ad"
      proof -
        have "address e\<^sub>l = adv" using msel_ssel_expr_load_rexp_gas(4)[OF 1(5)] adv_def by simp
        moreover have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        ultimately show ?thesis by simp
      qed
      moreover have "type (accounts st''' ad) = Some (Contract cname)"
      proof -
        have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        then have "type (accounts st ad) = type (acc ad)" using transfer_type_same[OF 1(6)] adv_def by simp
        then show ?thesis using l12 st'''_def by simp
      qed
      moreover have "iv (storage st''' ad) \<lceil>bal (accounts st''' ad)\<rceil>"
      proof -
        have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        then have "bal (accounts st ad) = bal (accounts st''' ad)" using transfer_eq[OF 1(6), of ad] l1 using st'''_def adv_def by simp
        moreover have "storage st ad = storage st''' ad" using st'''_def `adv \<noteq> ad` by simp
        ultimately show ?thesis using l2 by simp
      qed
      moreover have "local.stmt (snd cn) e\<^sub>l cd\<^sub>l st''' = Normal ((), st'')" using 1(7) st'''_def adv_def by simp
      moreover have "aux1 st'''"
      proof -
        have *: "gas st''' \<le> gas st" unfolding st'''_def using msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] msel_ssel_expr_load_rexp_gas(4)[OF 1(5)] by auto
        then show ?thesis using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by simp
      qed
      moreover have "aux2 st'''"
      proof -
        have *: "gas st''' \<le> gas st" unfolding st'''_def using msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] msel_ssel_expr_load_rexp_gas(4)[OF 1(5)] by auto
        then show ?thesis using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by simp
      qed
      ultimately have "iv (storage st'' ad) \<lceil>bal (accounts st'' ad)\<rceil>" by simp
      moreover have "storage st'' ad = storage st' ad" using 1(8) by simp
      moreover have "bal (accounts st'' ad) = bal (accounts st' ad)" using 1(8) by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

type_synonym Precondition = "int \<times> StorageT \<times> Environment \<times> Memoryvalue Store \<times> Stackvalue Store \<times> Memoryvalue Store \<Rightarrow> bool"
type_synonym Postcondition = "int \<times> StorageT \<Rightarrow> bool"

text \<open>
  The following lemma can be used to verify (recursive) internal or external method calls and transfers executed from **inside** (@{term "address ev = ad"}).
  In particular the lemma requires the contract to be annotated as follows:
  \<^item> Pre/Postconditions for internal methods
  \<^item> Invariants for external methods 

  The lemma then requires us to verify the following:
  \<^item> Postconditions from preconditions for internal method bodies.
  \<^item> Invariants hold for external method bodies.

  To this end it allows us to assume the following:
  \<^item> Preconditions imply postconditions for internal method calls.
  \<^item> Invariants hold for external method calls for other contracts external methods.
\<close>

definition Pe
  where "Pe ad iv st \<equiv>
    (\<forall>ev ad' i xe val cd.
       address ev = ad \<and>
       (\<forall>adv c g v t g' v'.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) (gas st - costs (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         type (accounts st adv) = Some (Contract c) \<and>
         c |\<in>| fmdom ep \<and>
         expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt 256) v = Some v'
        \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (\<lambda>s. stmt (EXTERNAL ad' i xe val) ev cd s) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st)"

definition Pi
  where "Pi ad pre post st \<equiv>
    (\<forall>ev i xe cd.
       address ev = ad \<and>
       contract ev = cname \<and>
       (\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
         load False fp xe (ffold (init members) (emptyEnv ad (contract ev) (sender ev) (svalue ev)) (fmdom members)) emptyStore emptyStore (memory st) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)
        \<longrightarrow> pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l))
    \<longrightarrow> wpS (\<lambda>s. stmt (INVOKE i xe) ev cd s) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st)"

definition Pfi
  where "Pfi ad pref postf st \<equiv>
   (\<forall>ev ex ad' cd.
     address ev = ad \<and>
     (\<forall>adv g.
       expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
      \<longrightarrow> adv = ad) \<and>
     (\<forall>g v t g'.
       expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue ad, Value TAddr), g) \<and>
       expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')
      \<longrightarrow> pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad))
    \<longrightarrow> wpS (\<lambda>s. stmt (TRANSFER ad' ex) ev cd s) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st)"

definition Pfe
  where "Pfe ad iv st \<equiv>
     (\<forall>ev ex ad' cd.
       address ev = ad \<and>
       (\<forall>adv g.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
        \<longrightarrow> adv \<noteq> ad) \<and>
       (\<forall>adv g v t g' v'.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt 256) v = Some v'
        \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (\<lambda>s. stmt (TRANSFER ad' ex) ev cd s) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st)"

lemma wp_external_invoke_transfer:
    fixes pre::"Identifier \<Rightarrow> Precondition"
      and post::"Identifier \<Rightarrow> Postcondition"
      and pref::"Postcondition"
      and postf::"Postcondition"
      and iv::"Invariant"
    assumes assm: "\<And>st::State.
    \<lbrakk>\<forall>st'::State. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname)
        \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "type (accounts st ad) = Some (Contract cname) \<longrightarrow> Pe ad iv st \<and> Pi ad pre post st \<and> Pfi ad pref postf st \<and> Pfe ad iv st"
proof (induction st rule: gas_induct)
  case (1 st)
  show ?case unfolding Pe_def Pi_def Pfi_def Pfe_def
  proof elims
    fix ev::Environment and ad' i xe val cd
    assume a00: "type (accounts st ad) = Some (Contract cname)"
       and a0: "address ev = ad"
       and a1: "\<forall>adv c g v t g' v'.
          local.expr ad' ev cd (st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>)
           (gas st - costs (EXTERNAL ad' i xe val) ev cd st) =
          Normal ((KValue adv, Value TAddr), g) \<and>
          adv \<noteq> ad \<and>
          type (accounts st adv) = Some (Contract c) \<and>
          c |\<in>| fmdom ep \<and>
          local.expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt 256) v = Some v'
      \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    show "wpS (local.stmt (EXTERNAL ad' i xe val) ev cd) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st" unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a s''''''
      assume "x1 = (x1a, s'''''')" and 2: "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal x1"
      then have "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal (x1a, s'''''')" by simp
      then show "gas s'''''' \<le> gas st \<and> iv (storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts s'''''' ad)))"
      proof (cases rule: external)
        case (Some adv0 c0 g0 ct0 cn0 fb0 v0 t0 g0' v0' fp0 f0 e\<^sub>l0 cd\<^sub>l0 k\<^sub>l0 m\<^sub>l0 g0'' acc0 st0'')
        moreover have "iv (storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st0'' ad)))"
        proof -
          from Some(3) have "adv0 \<noteq> ad" using a0 by simp
          then have "address e\<^sub>l0 \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] ffold_init_ad_same[of ct0 "(emptyEnv adv0 c0 (address ev) v0')" "(fmdom ct0)" "(ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0) (fmdom ct0))"] unfolding emptyEnv_def by simp
          moreover have "type (accounts (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>) ad) = Some (Contract cname)" using transfer_type_same[OF Some(10)] a00 by simp
          moreover have "iv (storage (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>) ad)
                        (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>) ad)))"
          proof -
            from Some(5) have "c0 |\<in>| fmdom ep" by (rule fmdomI)
            with a0 a1 Some `adv0 \<noteq> ad` have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by simp
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF Some(10)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>) \<longrightarrow>
              (\<forall>mid fp f ev.
                members $$ mid = Some (Method (fp, True, f)) \<and>
                address ev \<noteq> ad
               \<longrightarrow> (\<forall>adex cd st0 xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l' m\<^sub>l' g'' acc.
                     g'' \<le> gas st' \<and>
                     type (acc ad) = Some (Contract cname) \<and>
                     local.expr adex ev cd (st0\<lparr>gas := gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>) (gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g) \<and>
                     local.expr val ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt 256) v = Some v' \<and>
                     local.load True fp xe (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l', m\<^sub>l'), g'') \<and>
                     transfer (address ev) ad v' (accounts (st0\<lparr>gas := g''\<rparr>)) = Some acc \<and>
                     iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
                    \<longrightarrow>  wpS (local.stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l', memory := m\<^sub>l'\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::State
            assume "gas st' < gas (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] msel_ssel_expr_load_rexp_gas(3)[OF Some(2)] msel_ssel_expr_load_rexp_gas(3)[OF Some(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct1] unfolding Qe_def by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>) \<longrightarrow>
              (\<forall>ev. address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> gas st' \<and>
                     type (acc ad) = Some (Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>gas := gas st0 - cc\<rparr>) (gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt 256) v = Some v' \<and>
                     transfer (address ev) ad v' (accounts st0) = Some acc \<and>
                     iv (storage st0 ad) (\<lceil>bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS (local.stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore)
                      (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (st0\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::State
            assume l0: "gas st' < gas (st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] msel_ssel_expr_load_rexp_gas(3)[OF Some(2)] msel_ssel_expr_load_rexp_gas(3)[OF Some(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed
          ultimately show ?thesis using safeStore[of e\<^sub>l0 ad "st\<lparr>gas := g0'', accounts := acc0, stack := k\<^sub>l0, memory := m\<^sub>l0\<rparr>" iv f0 cd\<^sub>l0 st0''] Some unfolding Qe_def Qfe_def by blast
        qed
        moreover have "gas st0'' \<le> gas st" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9),THEN conjunct1] msel_ssel_expr_load_rexp_gas(3)[OF Some(2)] msel_ssel_expr_load_rexp_gas(3)[OF Some(6)] stmt_gas[OF Some(11)] by simp
        ultimately show ?thesis by simp
      next
        case (None adv0 c0 g0 ct0 cn0 fb0' v0 t0 g0' v0' acc0 st0'')
        moreover have "iv (storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts s'''''' ad)))"
        proof -
          from None have "adv0 \<noteq> ad" using a0 by auto
          then have "address (ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)) \<noteq> ad" using ffold_init_ad_same[where ?e="\<lparr>address = adv0, contract = c0, sender = address ev, svalue = v0', denvalue = {$$}\<rparr>" and e'="ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)"] unfolding emptyEnv_def by simp
          moreover have "type (accounts (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad) = Some (Contract cname)" using transfer_type_same[OF None(9)] a00 by simp
          moreover have "iv (storage (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad)))"
          proof -
            from None(5) have "c0 |\<in>| fmdom ep" by (rule fmdomI)
            with a0 a1 None `adv0 \<noteq> ad` have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by simp
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF None(9)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow>
              (\<forall>mid fp f ev.
                members $$ mid = Some (Method (fp, True, f)) \<and>
                address ev \<noteq> ad
               \<longrightarrow> (\<forall>adex cd st0 xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l' m\<^sub>l' g'' acc.
                     g'' \<le> gas st' \<and>
                     type (acc ad) = Some (Contract cname) \<and>
                     local.expr adex ev cd (st0\<lparr>gas := gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>) (gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g) \<and>
                     local.expr val ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt 256) v = Some v' \<and>
                     local.load True fp xe (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l', m\<^sub>l'), g'') \<and>
                     transfer (address ev) ad v' (accounts (st0\<lparr>gas := g''\<rparr>)) = Some acc \<and>
                     iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
                    \<longrightarrow>  wpS (local.stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l', memory := m\<^sub>l'\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::State
            assume "gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF None(2)] msel_ssel_expr_load_rexp_gas(3)[OF None(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct1] unfolding Qe_def by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow>
              (\<forall>ev. address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> gas st' \<and>
                     type (acc ad) = Some (Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>gas := gas st0 - cc\<rparr>) (gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt 256) v = Some v' \<and>
                     transfer (address ev) ad v' (accounts st0) = Some acc \<and>
                     iv (storage st0 ad) (\<lceil>bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS (local.stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore)
                      (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (st0\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::State
            assume l0: "gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF None(2)] msel_ssel_expr_load_rexp_gas(3)[OF None(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed                                                                                                                                                                                                                                                                                                            
          ultimately have "iv (storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st0'' ad)))" using safeStore[of "ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)" ad "st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>" iv fb0' emptyStore "st0''"] None unfolding Qe_def Qfe_def by blast
          then show ?thesis using None(11) by simp
        qed
        moreover have "gas st0'' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF None(2)] msel_ssel_expr_load_rexp_gas(3)[OF None(6)] stmt_gas[OF None(10)] by simp
        ultimately show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (EXTERNAL ad' i xe val) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using Ex.nchotomy by simp
    qed
  next
    fix ev ex ad' cd
    assume a00: "type (accounts st ad) = Some (Contract cname)"
      and a0: "address ev = ad"
      and a1: "\<forall>adv g. local.expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<longrightarrow> adv \<noteq> ad"
      and a2: "\<forall>adv g v t g' v'.
          local.expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
          adv \<noteq> ad \<and>
          local.expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt 256) v = Some v' \<longrightarrow>
          iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    show "wpS (local.stmt (TRANSFER ad' ex) ev cd) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a s''''''
      assume "x1 = (x1a, s'''''')" and "local.stmt (TRANSFER ad' ex) ev cd st = Normal x1"
      then have 2: "local.stmt (TRANSFER ad' ex) ev cd st = Normal (x1a, s'''''')" by simp
      then show "gas s'''''' \<le> gas st \<and> iv (storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts s'''''' ad)))"
      proof (cases rule: transfer)
        case (Contract v0 t0 g0 adv0 c0 g0' v0' acc0 ct0 cn0 f0 st0'')
        moreover have "iv (storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts s'''''' ad)))"
        proof -
          from Contract have "adv0 \<noteq> ad" using a1 by auto
          then have "address (ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)) \<noteq> ad" using a0 ffold_init_ad_same[where ?e'="ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)"] unfolding emptyEnv_def by simp
          moreover have "type (accounts (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad) = Some (Contract cname)" using transfer_type_same[OF Contract(7)] a00 by simp
          moreover have "iv (storage (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) ad)))"
          proof -
            from a0 a2 Contract `adv0 \<noteq> ad` have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by blast
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF Contract(7)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow> Qe ad iv st'"
          proof (rule allI,rule impI)
            fix st'::State
            assume "gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by auto
            then show "Qe ad iv st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct1] by simp
          qed
          moreover have "\<forall>st'::State. gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow>
              (\<forall>ev. address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> gas st' \<and>
                     type (acc ad) = Some (Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>gas := gas st0 - cc\<rparr>) (gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt 256) v = Some v' \<and>
                     transfer (address ev) ad v' (accounts st0) = Some acc \<and>
                     iv (storage st0 ad) (\<lceil>bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS (local.stmt fb (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore)
                      (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (st0\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::State
            assume l0: "gas st' < gas (st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>)"
            then have "gas st' < gas st" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `gas st' < gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed
          ultimately have "iv (storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st0'' ad)))" using safeStore[of "ffold (init ct0) (emptyEnv adv0 c0 (address ev) v0') (fmdom ct0)" ad "st\<lparr>gas := g0', accounts := acc0, stack := emptyStore, memory := emptyStore\<rparr>" iv f0 emptyStore "st0''"] Contract unfolding Qe_def Qfe_def by blast
          then show ?thesis using Contract(9) by simp
        qed
        moreover have "gas st0'' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] stmt_gas[OF Contract(8)] by simp
        ultimately show ?thesis by simp
      next
        case (EOA v0 t0 g0 adv0 g0' v0' acc0)
        moreover have "iv (storage (st\<lparr>gas := g0', accounts := acc0\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts (st\<lparr>gas := g0', accounts := acc0\<rparr>) ad)))"
        proof -
          from EOA have "adv0 \<noteq> ad" using a1 by auto
          with a0 a2 EOA have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by blast
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF EOA(6)] a0 `adv0 \<noteq> ad` by simp
          ultimately show ?thesis by simp
        qed
        moreover have "g0' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF EOA(2)] msel_ssel_expr_load_rexp_gas(3)[OF EOA(3)] by simp
        ultimately show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (TRANSFER ad' ex) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using Ex.nchotomy by simp
    qed
  next
    fix ev i xe cd fp
    assume a0: "type (accounts st ad) = Some (Contract cname)"
       and ad_ev: "address ev = ad"
       and a1: "contract ev = cname"
       and pre: "\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
          local.load False fp xe (ffold (init members) (emptyEnv ad (contract ev) (sender ev) (svalue ev)) (fmdom members)) emptyStore emptyStore (memory st) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g) \<longrightarrow>
          pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)"
    show "wpS (local.stmt (INVOKE i xe) ev cd) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a st'
      assume "x1 = (x1a, st')"
         and *: "local.stmt (INVOKE i xe) ev cd st = Normal x1"
      then have "local.stmt (INVOKE i xe) ev cd st = Normal (x1a, st')" by simp
      then show "gas st' \<le> gas st \<and> post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)), storage st' ad)"
      proof (cases rule: invoke)
        case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
        have "post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)), storage st' ad)"
        proof -
          from * have "gas st > costs (INVOKE i xe) ev cd st" by (simp add:stmt.simps split:if_split_asm)
          then have "gas (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) < gas st" using invoke_not_zero[of i xe ev cd st] by simp

          from a1 have "ct = members" using 1(2) C1 by simp
          then have **: "local.load False fp xe (ffold (init members) (emptyEnv ad (contract ev) (sender ev) (svalue ev)) (fmdom members)) emptyStore
          emptyStore (memory st) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)
          (gas st - costs (INVOKE i xe) ev cd st) =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)" using 1(4) ad_ev by simp
          moreover from 1(2,3) have ***: "members $$ i = Some (Method (fp, False, f))" using ad_ev `ct = members` by simp
          ultimately have "pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)" using pre by blast
          moreover have "g \<le> gas (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)" using msel_ssel_expr_load_rexp_gas(4)[OF 1(4),THEN conjunct1] by simp
          ultimately have "wpS (local.stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err)
            (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using assm[OF all_gas_le[OF `gas (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) < gas st` "1.IH"], THEN conjunct2, THEN conjunct1] ** *** ad_ev a1 unfolding Qi_def by simp
          then show ?thesis unfolding wpS_def wp_def using 1(5,6) by simp
        qed
        moreover have "gas st' \<le> gas st" using msel_ssel_expr_load_rexp_gas(4)[OF 1(4),THEN conjunct1] stmt_gas[OF 1(5)] 1(6) by simp
        ultimately show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (INVOKE i xe) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using Ex.nchotomy by simp
    qed
  next
    fix ev ex ad' cd
    assume a0: "type (accounts st ad) = Some (Contract cname)"
      and ad_ev: "address ev = ad"
      and a1: "\<forall>adv g.
          local.expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)
           (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<longrightarrow> adv = ad"
      and a2: "\<forall>g v t g'.
          local.expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)
           (gas st - costs (TRANSFER ad' ex) ev cd st) =
          Normal ((KValue ad, Value TAddr), g) \<and>
          local.expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<longrightarrow>
          pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)"
    show "wpS (local.stmt (TRANSFER ad' ex) ev cd) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a st'
      assume "x1 = (x1a, st')" and "local.stmt (TRANSFER ad' ex) ev cd st = Normal x1"
      then have 2: "local.stmt (TRANSFER ad' ex) ev cd st = Normal (x1a, st')" by simp
      then show "gas st' \<le> gas st \<and> postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)), storage st' ad)"
      proof (cases rule: transfer)
        case (Contract v t g adv c g' v' acc ct cn f st'')
        moreover from Contract have "adv = ad" using a1 by auto
        ultimately have "pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)" using ad_ev a2 by auto
        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" using transfer_same[OF Contract(7)] `adv = ad` ad_ev by simp
        ultimately have "pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)), storage st ad)" by simp
        moreover from a0 have "c = cname" using Contract(5) `adv = ad` by simp
        then have "ct = members" and "f = fb" using C1 Contract(6) by simp+
        moreover have "gas st \<ge> costs (TRANSFER ad' ex) ev cd st" using 2 by (simp add:stmt.simps split:if_split_asm)
        then have "gas (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) < gas st" using transfer_not_zero[of ad' ex ev cd st] by simp
        moreover have "g' \<le> gas (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by simp
        ultimately have "wpS (local.stmt fb (ffold (init members) (emptyEnv ad c (address ev) v') (fmdom members)) emptyStore)
          (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err)
          (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using assm[OF all_gas_le[OF `gas (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) < gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct1] ad_ev Contract `adv = ad` `c = cname` unfolding Qfi_def by blast
        with `ct = members` `f=fb` have "gas st' \<le> gas (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) \<and> postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)), storage st' ad)" unfolding wpS_def wp_def using Contract(8,9) `adv = ad` by simp
        moreover from this have "gas st' \<le> gas st" using `g' \<le> gas (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)` by auto
        ultimately show ?thesis by simp
      next
        case (EOA v t g adv g' acc)
        then show ?thesis using a0 a1 by simp
      qed
    next
      fix e
      assume "local.stmt (TRANSFER ad' ex) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using Ex.nchotomy by simp
    qed
  qed
qed

text \<open>
  Refined versions of @{thm[source] wp_external_invoke_transfer}.
\<close>

lemma wp_transfer_ext[rule_format]:
  assumes "type (accounts st ad) = Some (Contract cname)"
      and "\<And>st::State. \<lbrakk>\<forall>st'::State. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "(\<forall>ev ex ad' cd.
       address ev = ad \<and>
       (\<forall>adv g.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
        \<longrightarrow> adv \<noteq> ad) \<and>
       (\<forall>adv g v t g' v'.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt 256) v = Some v'
        \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (\<lambda>s. stmt (TRANSFER ad' ex) ev cd s) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st)"
proof -
  from wp_external_invoke_transfer have "Pfe ad iv st" using assms by blast
  then show ?thesis using Pfe_def by simp
qed

lemma wp_external[rule_format]:
  assumes "type (accounts st ad) = Some (Contract cname)"
     and "\<And>st::State. \<lbrakk>\<forall>st'::State. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname)\<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
  shows "(\<forall>ev ad' i xe val cd.
       address ev = ad \<and>
       (\<forall>adv c g v t g' v'.
         expr ad' ev cd (st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) (gas st - costs (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         type (accounts st adv) = Some (Contract c) \<and>
         c |\<in>| fmdom ep \<and>
         expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt 256) v = Some v'
        \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (\<lambda>s. stmt (EXTERNAL ad' i xe val) ev cd s) (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) st)"
proof -
  from wp_external_invoke_transfer have "Pe ad iv st" using assms by blast
  then show ?thesis using Pe_def by simp
qed

lemma wp_invoke[rule_format]:
  assumes "type (accounts st ad) = Some (Contract cname)"
      and "\<And>st::State. \<lbrakk>\<forall>st'::State. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
  shows "(\<forall>ev i xe cd.
       address ev = ad \<and>
       contract ev = cname \<and>
       (\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
         load False fp xe (ffold (init members) (emptyEnv ad (contract ev) (sender ev) (svalue ev)) (fmdom members)) emptyStore emptyStore (memory st) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)
        \<longrightarrow> pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l))
    \<longrightarrow> wpS (\<lambda>s. stmt (INVOKE i xe) ev cd s) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st)"
proof -
  from wp_external_invoke_transfer have "Pi ad pre post st" using assms by blast
  then show ?thesis using Pi_def by simp
qed

lemma wp_transfer_int[rule_format]:
  assumes "type (accounts st ad) = Some (Contract cname)"
      and "\<And>st::State. \<lbrakk>\<forall>st'::State. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "(\<forall>ev ex ad' cd.
     address ev = ad \<and>
     (\<forall>adv g.
       expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
      \<longrightarrow> adv = ad) \<and>
     (\<forall>g v t g'.
       expr ad' ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue ad, Value TAddr), g) \<and>
       expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')
      \<longrightarrow> pref (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad))
    \<longrightarrow> wpS (\<lambda>s. stmt (TRANSFER ad' ex) ev cd s) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)), storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) st)"
proof -
  from wp_external_invoke_transfer have "Pfi ad pref postf st" using assms by blast
  then show ?thesis using Pfi_def by simp
qed

definition constructor :: "((String.literal, String.literal) fmap \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> bool"
  where "constructor iv \<equiv> (\<forall>acc g'' m\<^sub>l k\<^sub>l cd\<^sub>l e\<^sub>l g' t v xe i cd val st ev adv.
    adv = hash (address ev) (ShowL\<^sub>n\<^sub>a\<^sub>t (contracts (accounts st (address ev)))) \<and>
    type (accounts st adv) = None \<and>
    expr val ev cd (st\<lparr>gas := gas st - costs (NEW i xe val) ev cd st\<rparr>) (gas st - costs (NEW i xe val) ev cd st) = Normal ((KValue v, Value t), g') \<and>
    load True (fst const) xe (ffold (init members) (emptyEnv adv cname (address ev) v) (fmdom members)) emptyStore emptyStore emptyStore ev cd (st\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'') \<and>
    transfer (address ev) adv v (accounts (st\<lparr>accounts := (accounts st)(adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>)\<rparr>)) = Some acc
    \<longrightarrow> wpS (local.stmt (snd const) e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st adv) \<lceil>bal (accounts st adv)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
        (st\<lparr>gas := g'', storage:=(storage st)(adv := {$$}), accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>))"

lemma invariant_rec:
  fixes iv ad
  assumes "\<forall>ad (st::State). Qe ad iv st"
      and "\<forall>ad (st::State). Qfe ad iv st"
      and "constructor iv"
      and "address ev \<noteq> ad"
      and "type (accounts st ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))"
    shows "\<forall>(st'::State). stmt f ev cd st = Normal ((), st') \<and> type (accounts st' ad) = Some (Contract cname)
            \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
  using assms(4-)
proof (induction rule:stmt.induct)
  case (1 ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt SKIP ev cd st = Normal ((), st')"
       and "type (accounts st' ad) = Some (Contract cname)"
    then show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>" using 1 skip[OF *] by simp
  qed
next
  case (2 lv ex ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt (ASSIGN lv ex) ev cd st = Normal ((), st')"
       and "type (accounts st' ad) = Some (Contract cname)"
    then show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>" using 2 by (cases rule: assign[OF *];simp)
  qed
next
  case (3 s1 s2 ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt (COMP s1 s2) ev cd st = Normal ((), st')"
       and **: "type (accounts st' ad) = Some (Contract cname)"
      show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule: comp[OF *])
      case (1 st'')
      moreover from 3(4) have "type (accounts (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) = Some (Contract cname) \<longrightarrow> iv (storage (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) \<lceil>bal (accounts (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad)\<rceil>" by auto
      ultimately have "type (accounts st'' ad) = Some (Contract cname) \<longrightarrow> iv (storage st'' ad) \<lceil>bal (accounts st'' ad)\<rceil>" using 3(1)[OF _ _ 3(3)] by fastforce
      then show ?thesis using 3(2)[OF _ _ _ 3(3)] 1 ** by fastforce
    qed
  qed
next
  case (4 ex s1 s2 ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (ITE ex s1 s2) ev cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
      show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:ite[OF a1])
      case (1 g)
      have "\<forall>st'. local.stmt s1 ev cd (st\<lparr>gas := g\<rparr>) = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 4(1)) using 1 4(3) 4(4) by auto
      then show ?thesis using a2 1(3) by blast
    next
      case (2 g)
      have "\<forall>st'. local.stmt s2 ev cd (st\<lparr>gas := g\<rparr>) = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 4(2)) using 2 4(3) 4(4) true_neq_false[symmetric] by auto
      then show ?thesis using a2 2(3) by blast
    qed
  qed
next
  case (5 ex s0 ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (WHILE ex s0) ev cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
      show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:while[OF a1])
      case (1 g st'')
      have "\<forall>st'. local.stmt s0 ev cd (st\<lparr>gas := g\<rparr>) = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 5(1)) using 1 5(3) 5(4) by auto
      then have *: "type (accounts st'' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st'' ad) \<lceil>bal (accounts st'' ad)\<rceil>" using 1(3) by simp
      have "\<forall>st'. local.stmt (WHILE ex s0) ev cd st'' = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 5(2)) using 1 5(3) 5(4) * by auto
      then show ?thesis using a2 1(4) by blast
    next
      case (2 g)
      then show ?thesis using a2 5(4) by simp
    qed
  qed
next
  case (6 i xe ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (INVOKE i xe) ev cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:invoke[OF a1])
      case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
      from 6(2) have "ad \<noteq> address e\<^sub>l" using msel_ssel_expr_load_rexp_gas(4)[OF 1(4)] ffold_init_ad by simp
      have "\<forall>st'. local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>" apply (rule 6(1)) using 1 6(3) `ad \<noteq> address e\<^sub>l` by auto
      then show ?thesis using a2 1(5,6) by auto
    qed
  qed
next
  case (7 adex i xe val ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (EXTERNAL adex i xe val) ev cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:external[OF a1])
      case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "type (acc ad) = Some (Contract c)" using transfer_type_same[OF 1(10)] 1(4) by auto
        moreover from `type (acc ad) = Some (Contract c)` have "type (accounts st' ad) = Some (Contract c)" using atype_same[OF 1(11)] 1(12) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" using 1 C1 by simp
        moreover have "g'' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by linarith
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "type (accounts st ad) = Some (Contract cname)" using 1(4) True by simp
          have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using 7(4) `type (accounts st ad) = Some (Contract cname)` by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(10)] 7(3) True by simp
          ultimately show ?thesis by simp
        qed
        ultimately have "wpS (local.stmt f e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
        (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" using 1 True  using assms(1) 1(8) 7(3) unfolding Qe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 1(11,12) by simp
      next
        case False
        then have *: "ad \<noteq> address e\<^sub>l" using msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] ffold_init_ad by simp
        moreover have **:"type (acc ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) \<lceil>bal (acc ad)\<rceil>"
        proof
          assume "type (acc ad) = Some (Contract cname)"
          then have "type (accounts st ad) = Some (Contract cname)" using transfer_type_same[OF 1(10)] by simp
          then have "iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>" using 7(4) by simp
          moreover have "bal (acc ad) = bal (accounts st ad)" using transfer_eq[OF 1(10)] 7(3) False by simp
          ultimately show "iv (storage st ad) \<lceil>bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and>
         type (accounts st' ad) = Some (Contract cname) \<longrightarrow>  iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
          using 7(1) 1 by auto
        then show ?thesis using a2 1(11,12) by simp
      qed
    next
      case (2 adv c g ct cn fb' v t g' v' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "type (acc ad) = Some (Contract c)" using transfer_type_same[OF 2(9)] 2(4) by auto
        moreover from `type (acc ad) = Some (Contract c)` have "type (accounts st' ad) = Some (Contract c)" using atype_same[OF 2(10)] 2(11) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" and "fb'=fb" using 2 C1 by simp+
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "type (accounts st ad) = Some (Contract cname)" using 2(4) True by simp
          then have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using 7(4) by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 2(9)] 7(3) True by simp
          ultimately show "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')" by simp
        qed
        moreover have "g' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] by linarith
        ultimately have "wpS (local.stmt fb' (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore) (\<lambda>st. iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
        (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using assms(2) 7(3) 2 True unfolding Qfe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 2(10,11) by simp
      next
        case False
        moreover have **:"type (acc ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) \<lceil>bal (acc ad)\<rceil>"
        proof
          assume "type (acc ad) = Some (Contract cname)"
          then have "type (accounts st ad) = Some (Contract cname)" using transfer_type_same[OF 2(9)] by simp
          then have "iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>" using 7(4) by simp
          moreover have "bal (acc ad) = bal (accounts st ad)" using transfer_eq[OF 2(9)] 7(3) False by simp
          ultimately show "iv (storage st ad) \<lceil>bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt fb' (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st') \<and>
         type (accounts st' ad) = Some (Contract cname) \<longrightarrow>  iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
          using 7(2) 2 by auto
        then show ?thesis using a2 2(10,11) by simp
      qed
    qed
  qed
next
  case (8 ad' ex ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (TRANSFER ad' ex) ev cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:transfer[OF a1])
      case (1 v t g adv c g' v' acc ct cn f st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "type (acc ad) = Some (Contract c)" using transfer_type_same[OF 1(7)] 1(5) by auto
        moreover from `type (acc ad) = Some (Contract c)` have "type (accounts st' ad) = Some (Contract c)" using atype_same[OF 1(8)] 1(9) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" and "f=fb" using 1 C1 by simp+
        moreover have "g' \<le> gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] by linarith
        moreover have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "type (accounts st ad) = Some (Contract cname)" using 1(5) True by simp
          then have "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))" using 8(3) by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(7)] 8(2) True by simp
          ultimately show "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')" by simp
        qed
        ultimately have "wpS (local.stmt f (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore) (\<lambda>st. iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
        (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" using assms(2) 8(2) 1 True unfolding Qfe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 1(8,9) by simp
      next
        case False
        moreover have "type (acc ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) \<lceil>bal (acc ad)\<rceil>"
        proof
          assume "type (acc ad) = Some (Contract cname)"
          then have "type (accounts st ad) = Some (Contract cname)" using transfer_type_same[OF 1(7)] by simp
          then have "iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>" using 8(3) by simp
          moreover have "bal (acc ad) = bal (accounts st ad)" using transfer_eq[OF 1(7)] 8(2) False by simp
          ultimately show "iv (storage st ad) \<lceil>bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt f (ffold (init ct) (emptyEnv adv c (address ev) v') (fmdom ct)) emptyStore
          (st\<lparr>gas := g', accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st') \<and> type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>" using 8(1) 1 by auto
        then show ?thesis using a2 1(8, 9) by simp
      qed
    next
      case (2 v t g adv g' v' acc)
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then show ?thesis using 2(5,7) a2 transfer_type_same[OF 2(6)] by simp
      next
        case False
        then have "bal (acc ad) = bal (accounts st ad)" using transfer_eq[OF 2(6)] 8(2) by simp
        moreover have "type (accounts st ad) = Some (Contract cname)" using transfer_type_same[OF 2(6)] 2(7) a2 by simp
        then have "iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>" using 8(3) by simp
        ultimately show ?thesis using 2(7) by simp
      qed
    qed
  qed
next
  case (9 id0 tp s e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (BLOCK ((id0, tp), None) s) e cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:blockNone[OF a1])
      case (1 cd' mem' sck' e')
      have "address e' = address e" using decl_env[OF 1(2)] by simp
      have "\<forall>st'. local.stmt s e' cd' (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) e cd st, stack := sck',
           memory := mem'\<rparr>) = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 9(1)) using 1 9(2,3) `address e' = address e` by auto
      then show ?thesis using a2 1(3) by blast
    qed
  qed
next
  case (10 id0 tp ex' s e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (BLOCK ((id0, tp), Some ex') s) e cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:blockSome[OF a1])
      case (1 v t g cd' mem' sck' e')
      have "address e' = address e" using decl_env[OF 1(3)] by simp
      have "\<forall>st'. local.stmt s e' cd' (st\<lparr>gas := g, stack := sck', memory := mem'\<rparr>) = Normal ((), st') \<and>
          type (accounts st' ad) = Some (Contract cname) \<longrightarrow>
          iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
        apply (rule 10(1)) using 1 10(2,3) `address e' = address e` by auto
      then show ?thesis using a2 1(4) by blast
    qed
  qed
next
  case (11 i xe val e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (NEW i xe val) e cd st = Normal ((), st')"
       and a2: "type (accounts st' ad) = Some (Contract cname)"
    show "iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
    proof (cases rule:new[OF a1])
      case (1 v t g ct cn fb' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'')
      define adv where "adv = hash (address e) \<lfloor>contracts (accounts (st\<lparr>gas := gas st - costs (NEW i xe val) e cd st\<rparr>) (address e))\<rfloor>"
      then have "address e\<^sub>l = adv" using msel_ssel_expr_load_rexp_gas(4)[OF 1(5)] by simp 
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then show ?thesis
        proof (cases "i = cname")
          case t0: True
          then have "ct = members" and "cn = const" and "fb' = fb" using 1(4) C1 by simp+
          then have "wpS (local.stmt (snd const) e\<^sub>l cd\<^sub>l) (\<lambda>st. iv (storage st adv) \<lceil>bal (accounts st adv)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
                      (st\<lparr>gas := g', storage:=(storage st)(adv := {$$}), accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>)"
            using assms(3) 11(3) 1 True adv_def t0 unfolding constructor_def by auto
          then have "iv (storage st'' adv) \<lceil>bal (accounts st'' adv)\<rceil>" unfolding wpS_def wp_def using 1(7) `cn = const` adv_def by simp
          then show ?thesis using 1(8) True by simp
        next
          case False
          moreover have "type (accounts st' ad) = Some (Contract i)"
          proof -
            from `adv = ad` have "type (((accounts st) (adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>)) ad) = Some (Contract i)" by simp
            then have "type (acc ad) = Some (Contract i)" using transfer_type_same[OF 1(6)] adv_def by simp
            then have "type (accounts st'' ad) = Some (Contract i)" using atype_same[OF 1(7)] adv_def by simp
            then show ?thesis using 1(8) by simp
          qed
          ultimately show ?thesis using a2 by simp
        qed
      next
        case False
        moreover have *: "type (acc ad) = Some (Contract cname) \<longrightarrow> iv (storage (st\<lparr>storage:=(storage st)(adv := {$$}), accounts:=acc\<rparr>) ad) \<lceil>bal (acc ad)\<rceil>"
        proof
          assume "type (acc ad) = Some (Contract cname)"
          then have "type (((accounts st) (adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>)) ad) = Some (Contract cname)" using transfer_type_same[OF 1(6)] adv_def by simp
          then have "type ((accounts st) ad) = Some (Contract cname)" using False by simp
          then have "iv (storage st ad) \<lceil>bal (accounts st ad)\<rceil>" using 11(3) by simp
          then have "iv (storage (st\<lparr>storage:=(storage st)(adv := {$$})\<rparr>) ad) \<lceil>bal (accounts st ad)\<rceil>" using False by simp
          then show "iv (storage (st\<lparr>storage:=(storage st)(adv := {$$}), accounts:=acc\<rparr>) ad) \<lceil>bal (acc ad)\<rceil>" using transfer_eq[OF 1(6)] adv_def 11(2) False by simp
        qed
        ultimately have "\<forall>st'. stmt (snd cn) e\<^sub>l cd\<^sub>l (st\<lparr>gas := g', storage := (storage st) (adv := {$$}), accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and>
             type (accounts st' ad) = Some (Contract cname) \<longrightarrow> iv (storage st' ad) \<lceil>bal (accounts st' ad)\<rceil>"
          using 11(1)[where ?s'k4="st\<lparr>gas := g', storage := (storage st) (adv := {$$}), accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>"]
            1 adv_def `address e\<^sub>l = adv` False * by auto
        moreover have "type (accounts st'' ad) = Some (Contract cname)" using 1(8) a2 adv_def by auto
        ultimately show ?thesis using a2 1(6,7,8) adv_def by simp
      qed
    qed
  qed
qed

theorem invariant:
  fixes iv ad
  assumes "\<forall>ad (st::State). Qe ad iv st"
      and "\<forall>ad (st::State). Qfe ad iv st"
      and "constructor iv"
      and "\<forall>ad. address ev \<noteq> ad \<and> type (accounts st ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))"
    shows "\<forall>(st'::State) ad. stmt f ev cd st = Normal ((), st') \<and> type (accounts st' ad) = Some (Contract cname) \<and> address ev \<noteq> ad
            \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
  using assms invariant_rec by blast
end

context Calculus
begin

  named_theorems mcontract
  named_theorems external
  named_theorems internal

  section \<open>Verification Condition Generator\<close>
  
  text \<open>
    To use the verification condition generator first invoke the following rule on the original Hoare triple:
  \<close>
  method vcg_valid =
    rule wpS_valid,
    erule conjE,
    simp
  
  method external uses cases =
    unfold Qe_def,
    elims,
    (erule cases;simp)
  
  method fallback uses cases =
    unfold Qfe_def,
    elims,
    rule cases
  
  method constructor uses cases =
    unfold constructor_def,
    elims,
    rule cases,
    simp
  
  text \<open>
    Then apply the correct rules from the following set of rules.
  \<close>
  
  subsection \<open>Skip\<close>
  
  method vcg_skip =
    rule wp_Skip;(solve simp)?
  
  subsection \<open>Assign\<close>
  
  text \<open>
    The weakest precondition for assignments generates a lot of different cases.
    However, usually only one of them is required for a given situation.
  
    The following rule eliminates the wrong cases by proving that they lead to a contradiction.
    It requires two facts to be provided:
    \<^item> @{term expr_rule}: should be a theorem which evaluates the expression part of the assignment
    \<^item> @{term lexp_rule}: should be a theorem which evaluates the left hand side of the assignment
  
  
    Both theorems should assume a corresponding loading of parameters and all declarations which happen before the assignment.
  \<close>
  
  method vcg_insert_expr_lexp for ex::E and lv::L uses expr_rule lexp_rule =
    match premises in
      expr: "expr ex _ _ _ _ = _" and
      lexp: "lexp lv _ _ _ _ = _" \<Rightarrow>
        \<open>insert expr_rule[OF expr] lexp_rule[OF lexp]\<close>
  
  method vcg_insert_decl for ex::E and lv::L uses expr_rule lexp_rule =
    match premises in
      decl: "decl _ _ _ _ _ _ _ _ = _" (multi) \<Rightarrow>
        \<open>vcg_insert_expr_lexp ex lv expr_rule:expr_rule[OF decl] lexp_rule:lexp_rule[OF decl]\<close>
    \<bar> _ \<Rightarrow>
        \<open>vcg_insert_expr_lexp ex lv expr_rule:expr_rule lexp_rule:lexp_rule\<close>
  
  method vcg_insert_load for ex::E and lv::L uses expr_rule lexp_rule =
    match premises in
      load: "load _ _ _ _ _ _ _ _ _ _ _ = _" \<Rightarrow>
        \<open>vcg_insert_decl ex lv expr_rule:expr_rule[OF load] lexp_rule:lexp_rule[OF load]\<close>
    \<bar> _ \<Rightarrow>
        \<open>vcg_insert_decl ex lv expr_rule:expr_rule lexp_rule:lexp_rule\<close>
  
  method vcg_assign uses expr_rule lexp_rule =
    match conclusion in
      "wpS (stmt (ASSIGN lv ex) _ _) _ _ _" for lv ex \<Rightarrow>
        \<open>rule wp_Assign; 
          (solve \<open>(rule FalseE, simp,
            (vcg_insert_load ex lv expr_rule:expr_rule lexp_rule:lexp_rule)), simp\<close>
         | solve simp)?\<close>,
        simp
  
  subsection \<open>Composition\<close>
  
  method vcg_comp =
    rule wp_Comp; simp

  subsection \<open>Blocks\<close>
  
  method vcg_block_some =
    rule wp_blockSome; simp
end

locale VCG = Calculus +
  fixes pref::"Postcondition"
    and postf::"Postcondition"
    and pre::"Identifier \<Rightarrow> Precondition"
    and post::"Identifier \<Rightarrow> Postcondition"
begin

subsection \<open>Transfer\<close>
text \<open>
  The following rule can be used to verify an invariant for a transfer statement.
  It requires four term parameters:
  \<^item> @{term[show_types] "pref::Postcondition"}: Precondition for fallback method called internally
  \<^item> @{term[show_types] "postf::Postcondition"}: Postcondition for fallback method called internally
  \<^item> @{term[show_types] "pre::Identifier \<Rightarrow> Precondition"}: Preconditions for internal methods
  \<^item> @{term[show_types] "post::Identifier \<Rightarrow> Postcondition"}: Postconditions for internal methods


  In addition it requires 8 facts:
  \<^item> @{term fallback_int}: verifies *postcondition* for body of fallback method invoked *internally*.
  \<^item> @{term fallback_ext}: verifies *invariant* for body of fallback method invoked *externally*.
  \<^item> @{term cases_ext}: performs case distinction over *external* methods of contract @{term ad}.
  \<^item> @{term cases_int}: performs case distinction over *internal* methods of contract @{term ad}.
  \<^item> @{term cases_fb}: performs case distinction over *fallback* method of contract @{term ad}.
  \<^item> @{term different}: shows that address of environment is different from @{term ad}.
  \<^item> @{term invariant}: shows that invariant holds *before* execution of transfer statement.


  Finally it requires two lists of facts as parameters:
  \<^item> @{term external}: verify that the invariant is preserved by the body of external methods.
  \<^item> @{term internal}: verify that the postcondition holds after executing the body of internal methods.
\<close>

method vcg_prep =
  (rule allI)+,
  rule impI,
  (erule conjE)+

method vcg_body uses fallback_int fallback_ext cases_ext cases_int cases_fb =
  (rule conjI)?,
  match conclusion in
    "Qe _ _ _" \<Rightarrow>
      \<open>unfold Qe_def,
       vcg_prep,
       erule cases_ext;
        (vcg_prep,
         rule external;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qi _ _ _ _" \<Rightarrow>
      \<open>unfold Qi_def,
       vcg_prep,
       erule cases_fb;
        (vcg_prep,
         rule internal;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qfi _ _ _ _" \<Rightarrow>
      \<open>unfold Qfi_def,
       rule allI,
       rule impI,
       rule cases_int;
        (vcg_prep,
         rule fallback_int;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qfe _ _ _" \<Rightarrow>
      \<open>unfold Qfe_def,
       rule allI,
       rule impI,
       rule cases_int;
        (vcg_prep,
         rule fallback_ext;
           solve \<open>assumption | simp\<close>)\<close>

method decl_load_rec for ad::Address and e::Environment uses eq decl load empty init =
  match premises in
    d: "decl _ _ _ _ _ _ _ (_, _, _, e') = Some (_, _, _, e)" for e'::Environment \<Rightarrow>
        \<open>decl_load_rec ad e' eq:trans_sym[OF eq decl[OF d]] decl:decl load:load empty:empty init:init\<close>
  \<bar> l: "load _ _ _ (ffold (init members) (emptyEnv ad cname (address e') v) (fmdom members)) _ _ _ _ _ _ _ = Normal ((e, _, _, _), _)" for e'::Environment and v \<Rightarrow>
        \<open>rule
          trans[
            OF eq
            trans[
              OF load[OF l]
              trans[
                OF init[of (unchecked) members "emptyEnv ad cname (address e') v" "fmdom members"]
                empty[of (unchecked) ad cname "address e'" v]]]]\<close>

method sameaddr for ad::Address =
  match conclusion in
    "address e = ad" for e::Environment \<Rightarrow>
      \<open>decl_load_rec ad e eq:refl[of "address e"] decl:decl_env[THEN conjunct1] load:msel_ssel_expr_load_rexp_gas(4)[THEN conjunct2, THEN conjunct1] init:ffold_init_ad empty:emptyEnv_address\<close>

lemma eq_neq_eq_imp_neq:
  "x = a \<Longrightarrow> b \<noteq> y \<Longrightarrow> a = b \<Longrightarrow> x \<noteq> y" by simp

method sender for ad::Address =
  match conclusion in
    "adv \<noteq> ad" for adv::Address \<Rightarrow>
      \<open>match premises in
        a: "address e' \<noteq> ad" and e: "expr SENDER e _ _ _ = Normal ((KValue adv, Value TAddr), _)" for e::Environment and e'::Environment \<Rightarrow>
          \<open>rule local.eq_neq_eq_imp_neq[OF expr_sender[OF e] a],
           decl_load_rec ad e eq:refl[of "sender e"] decl:decl_env[THEN conjunct2, THEN conjunct1] load:msel_ssel_expr_load_rexp_gas(4)[THEN conjunct2, THEN conjunct2, THEN conjunct1] init:ffold_init_sender empty:emptyEnv_sender\<close>\<close>

method vcg_init for ad::Address uses invariant =
  elims,
  sameaddr ad,
  sender ad,
  (rule invariant; assumption)

method vcg_transfer_ext for ad::Address
  uses fallback_int fallback_ext cases_ext cases_int cases_fb invariant =
  rule wp_transfer_ext[where pref = pref and postf = postf and pre = pre and post = post],
  solve simp,
  (vcg_body fallback_int:fallback_int fallback_ext:fallback_ext cases_ext:cases_ext cases_int:cases_int cases_fb:cases_fb)+,
  vcg_init ad invariant:invariant

end

end
