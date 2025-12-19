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
using assms by (simp add: stackvalue.split[of "\<lambda>x. wp x P E s"])

lemma wpmtypes[wprule]:
  assumes "\<And>i m. a = MTArray i m \<Longrightarrow> wp (f i m) P E s"
      and "\<And>t. a = MTValue t \<Longrightarrow> wp (g t) P E s"
    shows "wp (case a of MTArray i m \<Rightarrow> f i m | MTValue t \<Rightarrow> g t) P E s"
using assms by (simp add: mtypes.split[of "\<lambda>x. wp x P E s"])

lemma wpstypes[wprule]:
  assumes "\<And>i m. a = STArray i m \<Longrightarrow> wp (f i m) P E s"
      and "\<And>t t'. a = STMap t t' \<Longrightarrow> wp (g t t') P E s"
      and "\<And>t. a = STValue t \<Longrightarrow> wp (h t) P E s"
shows "wp (case a of STArray i m \<Rightarrow> f i m | STMap t t' \<Rightarrow> g t t' | STValue t \<Rightarrow> h t) P E s"
using assms by (simp add: stypes.split[of "\<lambda>x. wp x P E s"])

lemma wptype[wprule]:
  assumes "\<And>v. a = Value v \<Longrightarrow> wp (f v) P E s"
      and "\<And>m. a = Calldata m \<Longrightarrow> wp (g m) P E s"
      and "\<And>m. a = type.Memory m \<Longrightarrow> wp (h m) P E s"
      and "\<And>t. a = type.Storage t \<Longrightarrow> wp (i t) P E s"
shows "wp (case a of Value v \<Rightarrow> f v | Calldata m \<Rightarrow> g m | type.Memory m \<Rightarrow> h m | type.Storage s \<Rightarrow> i s) P E s"
  using assms by (simp add: type.split[of "\<lambda>x. wp x P E s"])

lemma wptypes[wprule]:
assumes "\<And>x. a= TSInt x \<Longrightarrow> wp (f x) P E s"
    and "\<And>x. a = TUInt x \<Longrightarrow> wp (g x) P E s"
    and "a = TBool \<Longrightarrow> wp h P E s"
    and "a = TAddr \<Longrightarrow> wp i P E s"
  shows "wp (case a of TSInt x \<Rightarrow> f x | TUInt x \<Rightarrow> g x | TBool \<Rightarrow> h | TAddr \<Rightarrow> i) P E s"
using assms by (simp add: types.split[of "\<lambda>x. wp x P E s"])

lemma wpltype[wprule]:
  assumes "\<And>l. a=LStackloc l \<Longrightarrow> wp (f l) P E s"
      and "\<And>l. a = LMemloc l \<Longrightarrow> wp (g l) P E s"
      and "\<And>l. a = LStoreloc l \<Longrightarrow> wp (h l) P E s"
    shows "wp (case a of LStackloc l \<Rightarrow> f l | LMemloc l \<Rightarrow> g l | LStoreloc l \<Rightarrow> h l) P E s"
using assms by (simp add: ltype.split[of "\<lambda>x. wp x P E s"])

lemma wpdenvalue[wprule]:
  assumes "\<And>l. a=Stackloc l \<Longrightarrow> wp (f l) P E s"
      and "\<And>l. a=Storeloc l \<Longrightarrow> wp (g l) P E s"
    shows "wp (case a of Stackloc l \<Rightarrow> f l | Storeloc l \<Rightarrow> g l) P E s"
  using assms by (simp add:denvalue.split[of "\<lambda>x. wp x P E s" f g a])

section \<open>Calculus\<close>

subsection \<open>Hoare Triples\<close>

context statement_with_gas
begin

type_synonym state_predicate = "accounts \<times> stack \<times> memoryT \<times> (address \<Rightarrow> storageT) \<Rightarrow> bool"

definition validS :: "state_predicate \<Rightarrow> s \<Rightarrow> state_predicate \<Rightarrow> (ex \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>\<^sub>S/ _ /(\<lbrace>_\<rbrace>\<^sub>S,/ \<lbrace>_\<rbrace>\<^sub>S)")
where
  "\<lbrace>P\<rbrace>\<^sub>S s \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S \<equiv>
     \<forall>st. P (Accounts st, Stack st, Memory st, Storage st)
     \<longrightarrow> (\<forall>ev cd. case stmt s ev cd st of
           Normal (_,st') \<Rightarrow> Q (Accounts st', Stack st', Memory st', Storage st')
         | Exception e \<Rightarrow> E e)"

definition wpS :: "s \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> (ex \<Rightarrow> bool) \<Rightarrow> environment \<Rightarrow> calldataT \<Rightarrow> state \<Rightarrow> bool"
  where "wpS s P E ev cd st \<equiv> wp (\<lambda>st. stmt s ev cd st) (\<lambda>_. P) E st"

lemma wpS_valid:
  assumes "\<And>ev cd (st::state). P (Accounts st, Stack st, Memory st, Storage st) \<Longrightarrow> wpS s (\<lambda>st. Q (Accounts st, Stack st, Memory st, Storage st)) E ev cd st"
  shows "\<lbrace>P\<rbrace>\<^sub>S s \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S"
  unfolding validS_def
  using assms unfolding wpS_def wp_def by simp

lemma valid_wpS:
  assumes "\<lbrace>P\<rbrace>\<^sub>S s \<lbrace>Q\<rbrace>\<^sub>S,\<lbrace>E\<rbrace>\<^sub>S"
  shows "\<And>ev cd st. P (Accounts st, Stack st, Memory st, Storage st) \<Longrightarrow> wpS s (\<lambda>st. Q (Accounts st, Stack st, Memory st, Storage st)) E ev cd st"
  unfolding wpS_def wp_def using assms unfolding validS_def by simp

subsection \<open>Skip\<close>

lemma wp_Skip:
  assumes "P (st\<lparr>Gas := state.Gas st - costs SKIP ev cd st\<rparr>)"
      and "E Gas"
    shows "wpS SKIP P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(1))
  apply wp
  using assms by simp+

subsection \<open>Assign\<close>

lemma wp_Assign1:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KValue rx \<and> is_LStackloc lx"
      and "\<And>v t g l t' g' v'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KValue v,Value t), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, Value t'), g');
            convert t t' v = Some v'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Stack:=updateStore l (KValue v') (Stack st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign2:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KValue rx \<and> is_LStoreloc lx"
      and "\<And>v t g l t' g' v'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KValue v,Value t), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc l, type.Storage (STValue t')), g');
            convert t t' v = Some v'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := (fmupd l v' (Storage st (Address ev))))\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign3:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KValue rx \<and> is_LMemloc lx"
      and "\<And>v t g l t' g' v'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KValue v, Value t), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LMemloc l, type.Memory (MTValue t')), g');
            convert t t' v = Some v'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory:=updateStore l (MValue v') (Memory st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign4:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KCDptr rx \<and> is_LStackloc lx \<and> is_Memory ly"
      and "\<And>p x t g l t' g' p' m' sv'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Memory t'), g');
            t' = MTArray x t;
            accessStore l (state.Stack st) = Some (KMemptr p');
            sv' = updateStore l (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st)))) (state.Stack st);
            cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) x t cd (snd (allocate(state.Memory st))) = Some m'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory := m', Stack := sv'\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign5:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KCDptr rx \<and> is_LStackloc lx \<and> is_Storage ly"
      and "\<And>p x t g l t' g' p' s'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Storage t'), g');
            accessStore l (Stack st) = Some (KStoptr p');
            cpm2s p p' x t cd (Storage st (Address ev)) = Some s'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := s')\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign6:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KCDptr rx \<and> is_LStoreloc lx"
      and "\<And>p x t g l t' g' s'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
            cpm2s p l x t cd (Storage st (Address ev)) = Some s'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := s')\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign7:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KCDptr rx \<and> is_LMemloc lx"
      and "\<And>p x t g l t' g' m m'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KCDptr p, Calldata (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LMemloc l, type.Memory t'), g');
            t' = MTArray x t;
            cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) x t cd (snd (allocate(state.Memory st))) = Some m;
            m' = updateStore l (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st)))) m\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory := m'\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign8:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KMemptr rx \<and> is_LStackloc lx \<and> is_Memory ly"
      and "\<And>p x t g l t' g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KMemptr p, type.Memory (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Memory t'), g')\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Stack:=updateStore l (KMemptr p) (Stack st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign9:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KMemptr rx \<and> is_LStackloc lx \<and> is_Storage ly"
      and "\<And>p x t g l t' g' p' s'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KMemptr p, type.Memory (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Storage t'), g');
            accessStore l (Stack st) = Some (KStoptr p');
            cpm2s p p' x t (Memory st) (Storage st (Address ev)) = Some s'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := s')\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign10:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KMemptr rx \<and> is_LStoreloc lx"
      and "\<And>p x t g l t' g' s'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KMemptr p, type.Memory (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
            cpm2s p l x t (Memory st) (Storage st (Address ev)) = Some s'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := s')\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign11:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KMemptr rx \<and> is_LMemloc lx"
      and "\<And>p x t g l t' g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KMemptr p, type.Memory (MTArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LMemloc l, t'), g')\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory:=updateStore l (MPointer p) (Memory st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign12:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KStoptr rx \<and> (\<exists>rt. ry = type.Storage rt \<and> is_STArray rt) \<and> is_LStackloc lx \<and> is_Memory ly"
      and "\<And>p x t g l t' g' p' m sv'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KStoptr p, type.Storage (STArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Memory t'), g');
            cps2mTypeCompatible (STArray x t) t';
            accessStore l (state.Stack st) = Some (KMemptr p');
            sv' = updateStore l (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st)))) (state.Stack st);
            cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) x t (state.Storage st (Address ev)) (snd (allocate(state.Memory st))) = Some m\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory := m, Stack := sv'\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign13:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KStoptr rx \<and> (\<exists>rt. ry = type.Storage rt \<and> is_STArray rt) \<and> is_LStackloc lx \<and> is_Storage ly"
      and "\<And>p x t g l t' g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KStoptr p, type.Storage (STArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, type.Storage t'), g')\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Stack:=updateStore l (KStoptr p) (Stack st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign14:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KStoptr rx \<and> is_LStoreloc lx"
      and "\<And>p x t g l t' g' s'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KStoptr p, type.Storage (STArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc l, t'), g');
            copy p l x t (Storage st (Address ev)) = Some s'\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Storage:=(Storage st) (Address ev := s')\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign15:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KStoptr rx \<and> is_LMemloc lx"
      and "\<And>p x t g l t' g' m m'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KStoptr p, type.Storage (STArray x t)), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LMemloc l, type.Memory t'), g');
            cps2mTypeCompatible (STArray x t) t';
            cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) x t (state.Storage st (Address ev)) (snd (allocate(state.Memory st))) = Some m;
            m' = updateStore l (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st)))) m\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Memory := m'\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

lemma wp_Assign16:
  fixes ex ev cd st lv
  defines "ngas \<equiv> state.Gas st - costs (ASSIGN lv ex) ev cd st"
  assumes "\<And>rx ry g lx ly g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((lx,ly), g')\<rbrakk>
          \<Longrightarrow> is_KStoptr rx \<and> (\<exists>rt. ry = type.Storage rt \<and> is_STMap rt) \<and> is_LStackloc lx"
      and "\<And>p t t' g l t'' g'.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((KStoptr p, type.Storage (STMap t t')), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStackloc l, t''), g')\<rbrakk>
          \<Longrightarrow> P (st\<lparr>Gas := g', Stack:=updateStore l (KStoptr p) (Stack st)\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Exception e \<Longrightarrow> E e"
      and "\<And>rx ry g e.
            \<lbrakk>expr ex ev cd (st\<lparr>Gas := ngas\<rparr>) ngas = Normal ((rx,ry), g);
            lexp lv ev cd (st\<lparr>Gas := g\<rparr>) g = Exception e\<rbrakk>
          \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "wpS (ASSIGN lv ex) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(2))
  apply wp
  using assms unfolding ngas_def by fastforce+

subsection \<open>Composition\<close>

lemma wp_Comp:
  assumes "wpS s1 (wpS s2 P E ev cd) E ev cd (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>)"
      and "E Gas"
    shows "wpS (COMP s1 s2) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(3))
  apply wp
  using assms unfolding wpS_def wp_def by simp_all

subsection \<open>Conditional\<close>

lemma wp_ITE:
  fixes ex s1 s2 ev cd st
  defines "nGas \<equiv> state.Gas st - costs (ITE ex s1 s2) ev cd st"
  assumes "\<And>g. expr ex ev cd (st\<lparr>Gas := nGas\<rparr>) nGas = Normal ((KValue \<lceil>True\<rceil>, Value TBool), g) \<Longrightarrow> wpS s1 P E ev cd (st\<lparr>Gas := g\<rparr>)"
      and "\<And>g. expr ex ev cd (st\<lparr>Gas := nGas\<rparr>) nGas = Normal ((KValue \<lceil>False\<rceil>, Value TBool), g) \<Longrightarrow> wpS s2 P E ev cd (st\<lparr>Gas := g\<rparr>)"
      and "\<And>e. expr ex ev cd (st\<lparr>Gas := nGas\<rparr>) nGas = Exception e \<Longrightarrow> E e"
      and "E Gas"
      and "E Err"
    shows "wpS (ITE ex s1 s2) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(4))
  apply wp
  using assms unfolding wpS_def by (simp_all)

subsection \<open>While Loop\<close>

lemma wp_While[rule_format]:
    fixes iv::"accounts \<times> stack \<times> memoryT \<times> (address \<Rightarrow> storageT) \<Rightarrow> bool"
      and ex sm ev cd
  defines "nGas st \<equiv> state.Gas st - costs (WHILE ex sm) ev cd st"
  assumes "\<And>st g. \<lbrakk>iv (Accounts st, Stack st, Memory st, Storage st); expr ex ev cd (st\<lparr>Gas := nGas st\<rparr>) (nGas st) = Normal ((KValue \<lceil>False\<rceil>, Value TBool), g)\<rbrakk> \<Longrightarrow> P (st\<lparr>Gas := g\<rparr>)"
      and "\<And>st g. \<lbrakk>iv (Accounts st, Stack st, Memory st, Storage st); expr ex ev cd (st\<lparr>Gas := nGas st\<rparr>) (nGas st) = Normal ((KValue \<lceil>True\<rceil>, Value TBool), g)\<rbrakk> \<Longrightarrow> wpS sm (\<lambda>st. iv (Accounts st, Stack st, Memory st, Storage st)) E ev cd (st\<lparr>Gas:=g\<rparr>)"
      and "\<And>st e. \<lbrakk>expr ex ev cd (st\<lparr>Gas := nGas st\<rparr>) (nGas st) = Exception e\<rbrakk> \<Longrightarrow> E e"
      and "\<And>st e. stmt sm ev cd st = Exception e \<Longrightarrow> E e"
      and "E Err"
      and "E Gas"
    shows "iv (Accounts st, Stack st, Memory st, Storage st) \<longrightarrow> wpS (WHILE ex sm) P E ev cd st"
proof (induction st rule:gas_induct)
  case (1 st)
  show ?case
  unfolding wpS_def wp_def
  proof (split result.split, rule conjI; rule allI; rule impI)
    fix x1 assume *: "local.stmt (WHILE ex sm) ev cd st = Normal x1"
    then obtain b g where **: "expr ex ev cd (st\<lparr>Gas := state.Gas st - costs (WHILE ex sm) ev cd st\<rparr>) (state.Gas st - costs (WHILE ex sm) ev cd st) = Normal ((KValue b, Value TBool), g)" by (simp only: stmt.simps, simp split:if_split_asm result.split_asm prod.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    with * consider (t) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True" | (f) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" by (simp add:stmt.simps split:if_split_asm result.split_asm prod.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    then show "iv (Accounts st, Stack st, Memory st, Storage st) \<longrightarrow> (case x1 of (r, s') \<Rightarrow> P s')"
    proof cases
      case t
      then obtain st' where ***: "stmt sm ev cd (st\<lparr>Gas := g\<rparr>) = Normal ((), st')" using * ** by (auto simp add:stmt.simps split:if_split_asm result.split_asm)
      then have ****: "local.stmt (WHILE ex sm) ev cd st' = Normal x1" using * ** t by (simp add:stmt.simps split:if_split_asm)
      show ?thesis
      proof
        assume "iv (Accounts st, Stack st, Memory st, Storage st)"
        then have "wpS sm (\<lambda>st. iv (Accounts st, Stack st, Memory st, Storage st)) E ev cd (st\<lparr>Gas:=g\<rparr>)" using nGas_def assms(3) ** t by auto
        then have "iv (Accounts st', Stack st', Memory st', Storage st')" unfolding wpS_def wp_def using *** by (simp split:result.split_asm)+
        moreover have "state.Gas st \<ge> costs (WHILE ex sm) ev cd st" using * by (simp add:stmt.simps split:if_split_asm)
        then have "state.Gas st' < state.Gas st" using stmt_gas[OF ***] msel_ssel_expr_load_rexp_gas(3)[OF **] while_not_zero[of ex sm ev cd st] by simp
        ultimately have "wpS (WHILE ex sm) P E ev cd st'" using 1 by simp
        then show "(case x1 of (r, s') \<Rightarrow> P s')" unfolding wpS_def wp_def using **** `state.Gas st' < state.Gas st` by auto
      qed
    next
      case f
      show ?thesis
      proof
        assume "iv (Accounts st, Stack st, Memory st, Storage st)"
        then have "P (st\<lparr>Gas := g\<rparr>)" using ** nGas_def assms(2) f by simp
        moreover have "x1 = ((),st\<lparr>Gas := g\<rparr>)" using * ** f by (simp add:stmt.simps true_neq_false[symmetric] split:if_split_asm)
        moreover have "g \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF **] by simp
        ultimately show "case x1 of (r, s') \<Rightarrow> P s'" by (auto split:prod.split)
      qed
    qed
  next
    fix e
    assume 0: "local.stmt (WHILE ex sm) ev cd st = Exception e"
    then show "iv (Accounts st, Stack st, Memory st, Storage st) \<longrightarrow> E e"
    proof (cases rule: whileE)
      case Gas
      then show ?thesis using assms(7) by simp
    next
      case Err
      then show ?thesis using assms(6) by simp
    next
      case Exp
      then show ?thesis using assms(4) nGas_def by simp
    next
      case (Stm g)
      then show ?thesis using assms(5) by auto
    next
      case (While g st')
      show ?thesis
      proof
        assume *: "iv (Accounts st, Stack st, state.Memory st, state.Storage st)"
        then have "iv (Accounts st', Stack st', state.Memory st', state.Storage st')" using assms(3)[OF *] unfolding wpS_def wp_def by (simp add:While(2,3) nGas_def split:result.split_asm prod.split_asm)
        moreover have "state.Gas st' < state.Gas st" using nGas_def[of st] while_not_zero[of ex sm ev cd st] stmt_gas[OF While(3)] msel_ssel_expr_load_rexp_gas(3)[OF While(2)] While(1) by simp
        ultimately have "wpS (WHILE ex sm) P E ev cd st'" using 1 by simp
        then show "E e" unfolding wpS_def wp_def by (simp add: While(4) split: result.split_asm prod.split_asm)
      qed
    qed
  qed
qed

subsection \<open>Blocks\<close>

lemma wp_blockNone:
    fixes id0 tp stm ev cd st
  defines "nGas \<equiv> state.Gas st - costs (BLOCK (id0, tp, None) stm) ev cd st"
  assumes "\<And>cd' mem' sck' e'. decl id0 tp None False cd (Memory st) (Storage st (Address ev))
           (cd, Memory st, Stack st, ev) = Some (cd', mem', sck', e')
          \<Longrightarrow> wpS stm P E e' cd' (st\<lparr>Gas := nGas, Stack := sck', Memory := mem'\<rparr>)"
      and "E Gas"
      and "E Err"
    shows "wpS (BLOCK (id0, tp, None) stm) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(9))
  apply wp
  using assms unfolding wpS_def by simp_all

lemma wp_blockSome:
    fixes id0 tp ex' stm ev cd st
  defines "nGas \<equiv> state.Gas st - costs (BLOCK (id0, tp, Some ex') stm) ev cd st"
  assumes "\<And>v t g' cd' mem' sck' e'.
         \<lbrakk>expr ex' ev cd (st\<lparr>Gas := nGas\<rparr>) nGas = Normal ((v, t), g');
          decl id0 tp (Some (v,t)) False cd (Memory st) (Storage st (Address ev)) (cd, Memory st, Stack st, ev) = Some (cd', mem', sck', e')\<rbrakk>
        \<Longrightarrow> wpS stm P E e' cd' (st\<lparr>Gas := g', Stack := sck', Memory := mem'\<rparr>)"
      and "\<And>e. expr ex' ev cd (st\<lparr>Gas := nGas\<rparr>) nGas = Exception e \<Longrightarrow> E e"
      and "E Gas"
      and "E Err"
    shows "wpS (BLOCK (id0, tp, Some ex') stm) P E ev cd st"
  unfolding wpS_def
  apply (subst stmt.simps(10))
  apply wp
  using assms unfolding wpS_def by (simp_all)

end

subsection \<open>External method invocation\<close>

locale Calculus = statement_with_gas +
  fixes cname::Identifier
    and members:: "(Identifier, member) fmap"
    and const::"(Identifier \<times> type) list \<times> s"
    and fb :: s
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

type_synonym invariant = "storageT \<Rightarrow> int \<Rightarrow> bool"

subsection \<open>Method invocations and transfer\<close>

definition Qe
  where "Qe ad iv st \<equiv>
    (\<forall>mid fp f ev.
       members $$ mid = Some (Method (fp,True,f)) \<and>
       Address ev \<noteq> ad
      \<longrightarrow> (\<forall>adex cd st' xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc.
            g'' \<le> state.Gas st \<and>
            Type (acc ad) = Some (atype.Contract cname) \<and>
            expr adex ev cd (st'\<lparr>Gas := state.Gas st' - costs (EXTERNAL adex mid xe val) ev cd st'\<rparr>) (state.Gas st' - costs (EXTERNAL adex mid xe val) ev cd st') = Normal ((KValue ad, Value TAddr), g) \<and>
            expr val ev cd (st'\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
            convert t (TUInt b256) v = Some v' \<and>
            load True fp xe (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore emptyStore emptyTypedStore ev cd (st'\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'') \<and>
            transfer (Address ev) ad v' (Accounts (st'\<lparr>Gas := g''\<rparr>)) = Some acc \<and>
            iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
           \<longrightarrow> wpS f (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g'', Accounts:= acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)))"

definition Qi
  where "Qi ad pre post st \<equiv>
   (\<forall>mid fp f ev.
     members $$ mid = Some (Method (fp,False,f)) \<and>
     Address ev = ad
    \<longrightarrow> (\<forall>cd st' i xe e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
          g \<le> state.Gas st \<and>
          load False fp xe (ffold (init members) (emptyEnv ad cname (Sender ev) (Svalue ev)) (fmdom members)) emptyTypedStore emptyStore (Memory st') ev cd (st'\<lparr>Gas := state.Gas st' - costs (INVOKE i xe) ev cd st'\<rparr>) (state.Gas st' - costs (INVOKE i xe) ev cd st') = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g) \<and>
          pre mid (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)), Storage st' ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)
         \<longrightarrow> wpS f (\<lambda>st. post mid (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)))"

definition Qfi
  where "Qfi ad pref postf st \<equiv>
   (\<forall>ev. Address ev = ad
    \<longrightarrow> (\<forall>ex cd st' adex cc v t g g' v' acc.
          g' \<le> state.Gas st \<and>
          expr adex ev cd (st'\<lparr>Gas := state.Gas st' - cc\<rparr>) (state.Gas st' - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
          expr ex ev cd (st'\<lparr>Gas := g\<rparr>) g= Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt b256) v = Some v' \<and>
          transfer (Address ev) ad v' (Accounts st') = Some acc \<and>
          pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)), Storage st' ad)
         \<longrightarrow> wpS fb (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st'\<lparr>Gas := g', Accounts := acc, Stack:=emptyStore, Memory:=emptyTypedStore\<rparr>)))"

definition Qfe
  where "Qfe ad iv st \<equiv>
   (\<forall>ev. Address ev \<noteq> ad
    \<longrightarrow> (\<forall>ex cd st' adex cc v t g g' v' acc.
          g' \<le> state.Gas st \<and>
          Type (acc ad) = Some (atype.Contract cname) \<and>
          expr adex ev cd (st'\<lparr>Gas := state.Gas st' - cc\<rparr>) (state.Gas st' - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
          expr ex ev cd (st'\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt b256) v = Some v' \<and>
          transfer (Address ev) ad v' (Accounts st') = Some acc \<and>
          iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
         \<longrightarrow> wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st'\<lparr>Gas := g', Accounts := acc, Stack:=emptyStore, Memory:=emptyTypedStore\<rparr>)))"

lemma safeStore[rule_format]:
  fixes ad iv
  defines "aux1 st \<equiv> \<forall>st'::state. state.Gas st' < state.Gas st \<longrightarrow> Qe ad iv st'"
      and "aux2 st \<equiv> \<forall>st'::state. state.Gas st' < state.Gas st \<longrightarrow> Qfe ad iv st'"
    shows "\<forall>st'. Address ev \<noteq> ad \<and> Type (Accounts st ad) = Some (atype.Contract cname) \<and> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad))) \<and>
            stmt f ev cd st = Normal ((), st') \<and> aux1 st \<and> aux2 st
           \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
proof (induction rule:stmt.induct[where ?P="\<lambda>f ev cd st. \<forall>st'. Address ev \<noteq> ad \<and> Type (Accounts st ad) = Some (atype.Contract cname) \<and> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad))) \<and> stmt f ev cd st = Normal ((), st') \<and> aux1 st \<and> aux2 st \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"])
  case (1 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and *: "local.stmt SKIP ev cd st = Normal ((), st')"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using skip[OF *] by simp
  qed
next
  case (2 lv ex ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume "Address ev \<noteq> ad" and "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and 3: "stmt (ASSIGN lv ex) ev cd st = Normal ((), st')"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" by (cases rule: assign[OF 3]; simp)
  qed
next
  case (3 s1 s2 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (COMP s1 s2) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof  (cases rule: comp[OF l3])
      case (1 st'')
      moreover have *:"assert Gas (\<lambda>st. costs (COMP s1 s2) ev cd st < state.Gas st) st = Normal ((), st)" using l3 by (simp add:stmt.simps split:if_split_asm)
      moreover from l2 have "iv (Storage (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad)))" by simp
      moreover have **:"state.Gas (st\<lparr>Gas:= state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) \<le> state.Gas st" by simp
      then have "aux1 (st\<lparr>Gas:= state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using 3(1) C1 l1 l12 by auto
      moreover from l12 have "Type (Accounts st'' ad) = Some (atype.Contract cname)" using atype_same[OF 1(2), of ad "atype.Contract cname"] l12 by auto
      moreover have **:"state.Gas st'' \<le> state.Gas st" using stmt_gas[OF 1(2)] by simp
      then have "aux1 st''" using 4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 st''" using 5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 3(2)[OF * _ 1(2), of "()"] 1(3) C1 l1 by simp
    qed
  qed
next
  case (4 ex s1 s2 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (ITE ex s1 s2) ev cd st = Normal ((), st')" and l4:"aux1 st" and l5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof (cases rule: ite[OF l3])
      case (1 g)
      moreover from l2 have "iv (Storage (st\<lparr>Gas :=g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g\<rparr>) ad)))" by simp
      moreover from l12 have "Type (Accounts (st\<lparr>Gas:= g\<rparr>) ad) = Some (atype.Contract cname)" using atype_same[OF 1(3), of ad "atype.Contract cname"] l12 by auto
      moreover have **:"state.Gas (st\<lparr>Gas:= g\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>Gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 4(1) l1 by simp
    next
      case (2 g)
      moreover from l2 have "iv (Storage (st\<lparr>Gas := g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g\<rparr>) ad)))" by simp
      moreover from l12 have "Type (Accounts (st\<lparr>Gas:= g\<rparr>) ad) = Some (atype.Contract cname)" using atype_same[OF 2(3), of ad "atype.Contract cname"] l12 by auto
      moreover have **:"state.Gas (st\<lparr>Gas:= g\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] by simp
      then have "aux1 (st\<lparr>Gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 4(2) l1 true_neq_false by simp
    qed
  qed
next
  case (5 ex s0 ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (WHILE ex s0) ev cd st = Normal ((), st')" and l4:"aux1 st" and l5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof (cases rule: while[OF l3])
      case (1 g st'')
      moreover from l2 have "iv (Storage (st\<lparr>Gas :=g\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g\<rparr>) ad)))" by simp
      moreover have *:"state.Gas (st\<lparr>Gas:= g\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>Gas:= g\<rparr>)" using l4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= g\<rparr>)" using l5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using 5(1) l1 l12 by simp
      moreover from l12 have "Type (Accounts st'' ad) = Some (atype.Contract cname)" using atype_same[OF 1(3), of ad "atype.Contract cname"] l12 by auto
      moreover have **:"state.Gas st'' \<le> state.Gas st" using stmt_gas[OF 1(3)] * by simp
      then have "aux1 st''" using l4 unfolding aux1_def using all_gas_less[OF _ **,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 st''" using l5 unfolding aux2_def using all_gas_less[OF _ **,of "\<lambda>st. Qfe ad iv st"] by blast
      ultimately show ?thesis using 5(2) 1(1,2,3,4) l1 by simp
    next
      case (2 g)
      then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using l2 by simp
    qed
  qed
next
  case (6 i xe ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume 1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and 2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and 3: "local.stmt (INVOKE i xe) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    from 3 obtain ct fb' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st''
      where l0: "costs (INVOKE i xe) ev cd st < state.Gas st"
      and l1: "ep $$ Contract ev = Some (ct, fb')"
      and l2: "ct $$ i = Some (Method (fp, False, f))"
      and l3: "load False fp xe (ffold (init ct) (emptyEnv (Address ev) (Contract ev) (Sender ev) (Svalue ev)) (fmdom ct)) emptyTypedStore emptyStore (Memory (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>)) ev cd (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) (state.Gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)"
      and l4: "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas:= g, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>) = Normal ((), st'')"
      and l5: "st' = st''\<lparr>Stack:=Stack st\<rparr>"
      using invoke by blast
    from 3 have *:"assert Gas (\<lambda>st. costs (INVOKE i xe) ev cd st < state.Gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
    moreover have **: "modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>)" by simp
    ultimately have "\<forall>st'. Address e\<^sub>l \<noteq> ad \<and> iv (Storage (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) ad))) \<and> local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<and> aux2 (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<longrightarrow>
      iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 6[OF * **] l1 l2 l3 l12 by (simp split:if_split_asm result.split_asm prod.split_asm option.split_asm)
    moreover have "Address (ffold (init ct) (emptyEnv (Address ev) (Contract ev) (Sender ev) (Svalue ev)) (fmdom ct)) = Address ev" using ffold_init_ad_same[of ct "(emptyEnv (Address ev) (Contract ev) (Sender ev) (Svalue ev))"] unfolding emptyEnv_def by simp
    with 1 have "Address e\<^sub>l \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by simp
    moreover from 2 have "iv (Storage (st\<lparr>Gas:= g, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas:= g, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>) ad)))" by simp
    moreover have *:"state.Gas (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by auto
    then have "aux1 (st\<lparr>Gas:= g, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
    moreover have *:"state.Gas (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(4)[OF l3] by auto
    then have "aux2 (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
    ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using l4 C1 by auto
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using l5  by simp
  qed
next
  case (7 ad' i xe val ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad"
      and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" 
      and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))"
      and 3: "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal ((), st')"
      and 4: "aux1 st" and 5:"aux2 st"
    show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof (cases rule: external[OF 3])
      case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover from this have "cname = c" using l12 1(4) by simp
        moreover from this have "members = ct" using C1 1(5) by simp
        moreover have "state.Gas st \<ge>  costs (EXTERNAL ad' i xe val) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "g'' < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] external_not_zero[of ad' i xe val ev cd st] by auto
        then have "Qe ad iv (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using 4 unfolding aux1_def by simp
        moreover have "g'' \<le> state.Gas (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" by simp
        moreover from l12 have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same[OF 1(10)] by simp
        moreover have "i |\<in>| fmdom members" using 1(8) `members = ct` by (simp add: fmdomI)
        moreover have "members $$ i = Some (Method (fp,True,f))" using 1(8) `members = ct` by simp
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(10)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        ultimately have "wpS f (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" unfolding Qe_def using l1 l12 1(2) 1(6-10) by simp
        moreover have "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st'')" using 1(11) by simp
        ultimately show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" unfolding wpS_def wp_def using 1(12) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (EXTERNAL ad' i xe val) ev cd st < state.Gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        moreover have **: "modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>)" by simp
        ultimately have "\<forall>st'. Address e\<^sub>l \<noteq> ad \<and> Type (acc ad) = Some (atype.Contract cname) \<and> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))) \<and> local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<and> aux2 (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 7(1)[OF * **] 1 by simp
        moreover have "Address (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) = adv" using ffold_init_ad_same[of ct "(emptyEnv adv c (Address ev) v)"] unfolding emptyEnv_def by simp
        with False have "Address e\<^sub>l \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by simp
        moreover have "Bal (acc ad) = Bal ((Accounts st) ad)" using transfer_eq[OF 1(10)] False l1 by simp
        then have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)))" using l2 by simp
        moreover have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same l12 1(10) by simp
        moreover have *:"state.Gas (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by auto
        then have "aux1 (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using 1(11) by simp
        then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 1(12) by simp
      qed
    next
      case (2 adv c g ct cn fb' v t g' v' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover have "state.Gas st \<ge>  costs (EXTERNAL ad' i xe val) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] external_not_zero[of ad' i xe val ev cd st] by simp
        then have "Qfe ad iv (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 5 unfolding aux2_def by simp
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 2(9)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        moreover have "g' \<le> state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" by simp
        moreover from l12 have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same[OF 2(9)] by simp
        ultimately have "wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" unfolding Qfe_def using l1 l12 2(2) 2(6-9) by blast
        moreover have "stmt fb (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st'')"
        proof -
          from True have "cname = c" using l12 2(4) by simp
          moreover from this have "fb'=fb" using C1 2(5) by simp
          moreover from True `cname = c` have "members = ct" using C1 2(5) by simp
          ultimately show ?thesis using 2(10) True by simp
        qed
        ultimately show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" unfolding wpS_def wp_def using 2(11) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (EXTERNAL ad' i xe val) ev cd st < state.Gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        then have "\<forall>st'. Address (ffold (init ct) (emptyEnv adv c (Address ev) v) (fmdom ct)) \<noteq> ad \<and>
          Type (acc ad) = Some (atype.Contract cname) \<and>
          iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))) \<and>
          local.stmt fb' (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st') \<and> aux1 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<and> aux2 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)
          \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 7(2)[OF *] 2 by simp
        moreover from False have "Address (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) \<noteq> ad" using ffold_init_ad_same[where ?e="\<lparr>Address = adv, Contract = c, Sender = Address ev, Svalue = v, Denvalue = {$$}\<rparr>" and ?e'="ffold (init ct) (emptyEnv adv c (Address ev) v) (fmdom ct)"] unfolding emptyEnv_def by simp
        moreover have "Bal (acc ad) = Bal ((Accounts st) ad)" using transfer_eq[OF 2(9)] False l1 by simp
        then have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)))"
          using l2 by simp
        moreover have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same l12 2(9) by simp
        moreover have *:"state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] by simp
        then have "aux1 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using 2(10) by simp
        then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 2(11) by simp
      qed
    qed
  qed
next
  case (8 ad' ex ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and 3: "local.stmt (TRANSFER ad' ex) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof (cases rule: transfer[OF 3])
      case (1 v t g adv c g' v' acc ct cn f st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        moreover have "state.Gas st \<ge>  costs (TRANSFER ad' ex) ev cd st" using 3 by (simp add:stmt.simps split:if_split_asm)
        then have "state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] transfer_not_zero[of ad' ex ev cd st] by auto
        then have "Qfe ad iv (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 5 unfolding aux2_def by simp
        moreover have "Sender (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) \<noteq> ad" using l1 ffold_init_ad_same[where ?e = "(emptyEnv adv c (Address ev) v')" and ?e'="ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)"] unfolding emptyEnv_def by simp
        moreover have "Svalue (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) = v'" using ffold_init_ad_same[where ?e = "(emptyEnv adv c (Address ev) v')" and ?e'="ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)", of ct "fmdom ct"] unfolding emptyEnv_def by simp
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using l2 by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(7)] l1 True by simp
          ultimately show ?thesis by simp
        qed
        moreover have "g' \<le> state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" by simp
        moreover from l12 have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same[OF 1(7)] by simp
        ultimately have "wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" unfolding Qfe_def using l1 l12 1(2-7) by blast
        moreover have "stmt fb (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st'')"
        proof -
          from True have "cname = c" using l12 1(5) by simp
          moreover from this have "f=fb" using C1 1(6) by simp
          moreover from True `cname = c` have "members = ct" using C1 1(6) by simp
          ultimately show ?thesis using 1(8) True by simp
        qed
        ultimately show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" unfolding wpS_def wp_def using 1(9) by simp
      next
        case False

        from 3 have *:"assert Gas (\<lambda>st. costs (TRANSFER ad' ex) ev cd st < state.Gas st) st = Normal ((), st)" by (simp add:stmt.simps split:if_split_asm)
        then have "\<forall>st'. Address (ffold (init ct) (emptyEnv adv c (Address ev) v) (fmdom ct)) \<noteq> ad \<and>
          Type (acc ad) = Some (atype.Contract cname) \<and>
          iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))) \<and>
          local.stmt f (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st') \<and>
          aux1 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<and> aux2 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)
          \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 8(1)[OF *] 1 by simp
        moreover from False have "Address (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) \<noteq> ad" using ffold_init_ad_same[of ct "emptyEnv adv c (Address ev) v"] unfolding emptyEnv_def by simp
        moreover have "Bal (acc ad) = Bal ((Accounts st) ad)" using transfer_eq[OF 1(7)] False l1 by simp
        then have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)))"
          using l2 by simp
        moreover have "Type (acc ad) = Some (atype.Contract cname)" using transfer_type_same l12 1(7) by simp
        moreover have *:"state.Gas (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] by simp
        then have "aux1 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
        moreover have "aux2 (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
        ultimately have "iv (Storage st'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st'' ad)))" using 1(8) C1 by simp
        then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 1(9) by simp
      qed
    next
      case (2 v t g adv g' v' acc)
      moreover from 2(5) have "adv \<noteq> ad" using C1 l12 by auto
      then have "Bal (acc ad) = Bal (Accounts st ad)" using transfer_eq[OF 2(6)] l1 by simp
      ultimately show ?thesis using l2 by simp
    qed
  qed
next
  case (9 id0 tp s ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (BLOCK (id0, tp, None) s) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof  (cases rule: blockNone[OF l3])
      case (1 cd' mem' sck' e')
      moreover from l2 have "iv (Storage (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) ev cd st, Stack := sck', Memory := mem'\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) ev cd st, Stack := sck', Memory := mem'\<rparr>) ad)))" by simp
      moreover have *:"state.Gas (st\<lparr>Gas:= state.Gas st - costs (BLOCK (id0, tp, None) s) ev cd st, Stack := sck', Memory := mem'\<rparr>) \<le> state.Gas st" by simp
      then have "aux1 (st\<lparr>Gas:= state.Gas st - costs (BLOCK (id0, tp, None) s) ev cd st, Stack := sck', Memory := mem'\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= state.Gas st - costs (BLOCK (id0, tp, None) s) ev cd st, Stack := sck', Memory := mem'\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      moreover have "Address e' \<noteq> ad" using decl_env[OF 1(2)] l1 by simp
      ultimately show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 9(1) l12 by simp
    qed
  qed
next
  case (10 id0 tp ex' s ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (BLOCK (id0, tp, Some ex') s) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof  (cases rule: blockSome[OF l3])
      case (1 v t g cd' mem' sck' e')
      moreover from l2 have "iv (Storage (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) ad)))" by simp
      moreover have *:"state.Gas (st\<lparr>Gas:= g, Stack := sck', Memory := mem'\<rparr>) \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] by simp
      then have "aux1 (st\<lparr>Gas:= g, Stack := sck', Memory := mem'\<rparr>)" using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by blast
      moreover have "aux2 (st\<lparr>Gas:= g, Stack := sck', Memory := mem'\<rparr>)" using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qfe ad iv st"] by blast
      moreover have "Address e' \<noteq> ad" using decl_env[OF 1(3)] l1 by simp
      ultimately show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))" using 10(1) l12 by simp
    qed
  qed
next
  case (11 i xe val ev cd st)
  show ?case
  proof (rule allI, rule impI, (erule conjE)+)
    fix st' assume l1: "Address ev \<noteq> ad" and l12:"Type (Accounts st ad) = Some (atype.Contract cname)" and l2: "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" and l3: "stmt (NEW i xe val) ev cd st = Normal ((), st')" and 4:"aux1 st" and 5:"aux2 st"
    then show "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
    proof  (cases rule: new[OF l3])
      case (1 v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'' v')
      define adv where "adv = hash_version (Address ev) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>state.Gas := state.Gas st - costs (NEW i xe val) ev cd st\<rparr>) (Address ev))))"
      define st0 where "st0 = st\<lparr>state.Gas := state.Gas st - costs (NEW i xe val) ev cd st\<rparr>"
      define st1 where "st1 = st\<lparr>state.Gas := g, Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (state.Storage st)(adv := {$$})\<rparr>"
      define st''' where "st''' = st\<lparr>state.Gas := g', Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (state.Storage st)(adv := {$$}), Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>"

      have a1: "assert Gas (\<lambda>st. costs (NEW i xe val) ev cd st < state.Gas st) st = Normal ((), st)"
        using 1(1) by simp
      have a2: "modify (\<lambda>st. st\<lparr>state.Gas := state.Gas st - costs (NEW i xe val) ev cd st\<rparr>) st = Normal ((), st0)"
        using st0_def by simp
      have a3: "applyf (\<lambda>st. hash_version (Address ev) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts st (Address ev))))) st0 = Normal (adv, st0)"
        using adv_def st0_def by simp
      have a4: "assert Err (\<lambda>st. Type (Accounts st adv) = None) st0 = Normal ((), st0)"
        using 1(2) adv_def st0_def by simp
      have a5: "toState (expr val ev cd) st0 = Normal ((KValue v, Value t), st0\<lparr>state.Gas := g\<rparr>)"
        using 1(3) st0_def by simp
      have a6: "(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | _ \<Rightarrow> throw Err) (st0\<lparr>state.Gas := g\<rparr>) = Normal ((v, t), st0\<lparr>state.Gas := g\<rparr>)"
        by simp
      have a7: "option Err (\<lambda>_. convert t (TUInt b256) v) (st0\<lparr>state.Gas := g\<rparr>) = Normal (v', st0\<lparr>state.Gas := g\<rparr>)"
        using 1(4) by simp
      have a8: "option Err (\<lambda>_. ep $$ i) (st0\<lparr>state.Gas := g\<rparr>) = Normal ((ct, cn, fb), st0\<lparr>state.Gas := g\<rparr>)"
        using 1(5) by simp
      have a9: "modify (\<lambda>st. st\<lparr>Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (state.Storage st)(adv := {$$})\<rparr>) (st0\<lparr>state.Gas := g\<rparr>) = Normal ((), st1)"
        using st0_def st1_def by simp
      define e' where "e' = ffold_init ct (emptyEnv adv i (Address ev) v') (fmdom ct)"
      have a10: "toState (load True (fst cn) xe e' emptyTypedStore emptyStore emptyTypedStore ev cd) st1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), st1\<lparr>state.Gas := g'\<rparr>)"
        using 1(6) st1_def e'_def adv_def st0_def by simp
      have a11: "option Err (\<lambda>st. transfer (Address ev) adv v' (Accounts st)) (st1\<lparr>state.Gas := g'\<rparr>) = Normal (acc, st1\<lparr>state.Gas := g'\<rparr>)"
        using 1(7) st1_def adv_def by simp
      have a12: "applyf (\<lambda>st. (Stack st, state.Memory st)) (st1\<lparr>state.Gas := g'\<rparr>) = Normal ((Stack st, state.Memory st), st1\<lparr>state.Gas := g'\<rparr>)"
        using st1_def by simp
      have a13: "modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (st1\<lparr>state.Gas := g'\<rparr>) = Normal ((), st''')"
        using st'''_def st1_def by simp

      have "\<forall>st'. Address e\<^sub>l \<noteq> ad \<and>
        Type (Accounts st''' ad) = Some (atype.Contract cname) \<and>
        iv (state.Storage st''' ad) \<lceil>Bal (Accounts st''' ad)\<rceil> \<and>
        local.stmt (snd cn) e\<^sub>l cd\<^sub>l st''' = Normal ((), st') \<and> aux1 st''' \<and> aux2 st''' \<longrightarrow>
        iv (state.Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
        using 11[OF a1 a2 a3 a4 a5 a6 refl a7 a8 refl refl a9 e'_def a10 refl refl refl a11 a12 refl a13] by simp
      moreover have "Address e\<^sub>l \<noteq> ad"
      proof -
        have "Address e\<^sub>l = adv" using msel_ssel_expr_load_rexp_gas(4)[OF 1(6)] adv_def by simp
        moreover have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        ultimately show ?thesis by simp
      qed
      moreover have "Type (Accounts st''' ad) = Some (atype.Contract cname)"
      proof -
        have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        then have "Type (Accounts st ad) = Type (acc ad)" using transfer_type_same[OF 1(7)] adv_def by simp
        then show ?thesis using l12 st'''_def by simp
      qed
      moreover have "iv (Storage st''' ad) \<lceil>Bal (Accounts st''' ad)\<rceil>"
      proof -
        have "adv \<noteq> ad" using l12 1(2) adv_def by auto
        then have "Bal (Accounts st ad) = Bal (Accounts st''' ad)" using transfer_eq[OF 1(7), of ad] l1 using st'''_def adv_def by simp
        moreover have "Storage st ad = Storage st''' ad" using st'''_def `adv \<noteq> ad` by simp
        ultimately show ?thesis using l2 by simp
      qed
      moreover have "local.stmt (snd cn) e\<^sub>l cd\<^sub>l st''' = Normal ((), st'')" using 1(8) st'''_def adv_def by simp
      moreover have "aux1 st'''"
      proof -
        have *: "state.Gas st''' \<le> state.Gas st" unfolding st'''_def using msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] msel_ssel_expr_load_rexp_gas(4)[OF 1(6)] by auto
        then show ?thesis using 4 unfolding aux1_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by simp
      qed
      moreover have "aux2 st'''"
      proof -
        have *: "state.Gas st''' \<le> state.Gas st" unfolding st'''_def using msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] msel_ssel_expr_load_rexp_gas(4)[OF 1(6)] by auto
        then show ?thesis using 5 unfolding aux2_def using all_gas_less[OF _ *,of "\<lambda>st. Qe ad iv st"] by simp
      qed
      ultimately have "iv (Storage st'' ad) \<lceil>Bal (Accounts st'' ad)\<rceil>" by simp
      moreover have "Storage st'' ad = Storage st' ad" using 1(9) by simp
      moreover have "Bal (Accounts st'' ad) = Bal (Accounts st' ad)" using 1(9) by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

type_synonym precondition = "int \<times> storageT \<times> environment \<times> (mtypes,memoryvalue) typedstore \<times> stackvalue store \<times> (mtypes,memoryvalue) typedstore \<Rightarrow> bool"
type_synonym postcondition = "int \<times> storageT \<Rightarrow> bool"

text \<open>
  The following lemma can be used to verify (recursive) internal or external method calls and transfers executed from **inside** (@{term "Address ev = ad"}).
  In particular the lemma requires the contract to be annotated as follows:
  \<^item> Pre/Postconditions for internal methods
  \<^item> Invariants for external methods 

  The lemma then requires us to verify the following:
  \<^item> Postconditions from preconditions for internal method bodies.
  \<^item> Invariants hold for external method bodies.

  To this end it allows us to assume the following:
  \<^item> Preconditions imply postconditions for internal method calls.
  \<^item> Invariants hold for external method calls for other Contracts external methods.
\<close>

definition Pe
  where "Pe ad iv st \<equiv>
    (\<forall>ev ad' i xe val cd.
       Address ev = ad \<and>
       (\<forall>adv c g v t g' v'.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) (state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         Type (Accounts st adv) = Some (atype.Contract c) \<and>
         c |\<in>| fmdom ep \<and>
         expr val ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt b256) v = Some v'
        \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (EXTERNAL ad' i xe val) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"

definition Pi
  where "Pi ad pre post st \<equiv>
    (\<forall>ev i xe cd.
       Address ev = ad \<and>
       Contract ev = cname \<and>
       (\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
         load False fp xe (ffold (init members) (emptyEnv ad (Contract ev) (Sender ev) (Svalue ev)) (fmdom members)) emptyTypedStore emptyStore (Memory st) ev cd (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) (state.Gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)
        \<longrightarrow> pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l))
    \<longrightarrow> wpS (INVOKE i xe) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"

definition Pfi
  where "Pfi ad pref postf st \<equiv>
   (\<forall>ev ex ad' cd.
     Address ev = ad \<and>
     (\<forall>adv g.
       expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
      \<longrightarrow> adv = ad) \<and>
     (\<forall>g v t g'.
       expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue ad, Value TAddr), g) \<and>
       expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g')
      \<longrightarrow> pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad))
    \<longrightarrow> wpS (TRANSFER ad' ex) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"

definition Pfe
  where "Pfe ad iv st \<equiv>
     (\<forall>ev ex ad' cd.
       Address ev = ad \<and>
       (\<forall>adv g.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
        \<longrightarrow> adv \<noteq> ad) \<and>
       (\<forall>adv g v t g' v'.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt b256) v = Some v'
        \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (TRANSFER ad' ex) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"

lemma wp_external_invoke_transfer:  
    fixes pre::"Identifier \<Rightarrow> precondition"
      and post::"Identifier \<Rightarrow> postcondition"
      and pref::"postcondition"
      and postf::"postcondition"
      and iv::"invariant"
    assumes assm: "\<And>st::state.
    \<lbrakk>\<forall>st'::state. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname)
        \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "Type (Accounts st ad) = Some (atype.Contract cname) \<longrightarrow> Pe ad iv st \<and> Pi ad pre post st \<and> Pfi ad pref postf st \<and> Pfe ad iv st"
proof (induction st rule: gas_induct)
  case (1 st)
  show ?case unfolding Pe_def Pi_def Pfi_def Pfe_def
  proof elims
    fix ev::environment and ad' i xe val cd
    assume a00: "Type (Accounts st ad) = Some (atype.Contract cname)"
       and a0: "Address ev = ad"
       and a1: "\<forall>adv c g v t g' v'.
          local.expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>)
           (state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st) =
          Normal ((KValue adv, Value TAddr), g) \<and>
          adv \<noteq> ad \<and>
          Type (Accounts st adv) = Some (atype.Contract c) \<and>
          c |\<in>| fmdom ep \<and>
          local.expr val ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt b256) v = Some v'
      \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    show "wpS (EXTERNAL ad' i xe val) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st" unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a s''''''
      assume "x1 = (x1a, s'''''')" and 2: "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal x1"
      then have "local.stmt (EXTERNAL ad' i xe val) ev cd st = Normal (x1a, s'''''')" by simp
      then show "iv (Storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts s'''''' ad)))"
      proof (cases rule: external)
        case (Some adv0 c0 g0 ct0 cn0 fb0 v0 t0 g0' v0' fp0 f0 e\<^sub>l0 cd\<^sub>l0 k\<^sub>l0 m\<^sub>l0 g0'' acc0 st0'')
        moreover have "iv (Storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st0'' ad)))"
        proof -
          from Some(3) have "adv0 \<noteq> ad" using a0 by simp
          then have "Address e\<^sub>l0 \<noteq> ad" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] ffold_init_ad_same[of ct0 "(emptyEnv adv0 c0 (Address ev) v0')" "(fmdom ct0)" "(ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0) (fmdom ct0))"] unfolding emptyEnv_def by simp
          moreover have "Type (Accounts (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>) ad) = Some (atype.Contract cname)" using transfer_type_same[OF Some(10)] a00 by simp
          moreover have "iv (Storage (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>) ad)
                        (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>) ad)))"
          proof -
            from Some(5) have "c0 |\<in>| fmdom ep" by (rule fmdomI)
            with a0 a1 Some `adv0 \<noteq> ad` have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by simp
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF Some(10)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>) \<longrightarrow>
              (\<forall>mid fp f ev.
                members $$ mid = Some (Method (fp, True, f)) \<and>
                Address ev \<noteq> ad
               \<longrightarrow> (\<forall>adex cd st0 xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l' m\<^sub>l' g'' acc.
                     g'' \<le> state.Gas st' \<and>
                     Type (acc ad) = Some (atype.Contract cname) \<and>
                     local.expr adex ev cd (st0\<lparr>Gas := state.Gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>) (state.Gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g) \<and>
                     local.expr val ev cd (st0\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt b256) v = Some v' \<and>
                     local.load True fp xe (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore emptyStore emptyTypedStore ev cd (st0\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l', m\<^sub>l'), g'') \<and>
                     transfer (Address ev) ad v' (Accounts (st0\<lparr>Gas := g''\<rparr>)) = Some acc \<and>
                     iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
                    \<longrightarrow>  wpS f (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l', Memory := m\<^sub>l'\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::state
            assume "state.Gas st' < state.Gas (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] msel_ssel_expr_load_rexp_gas(3)[OF Some(2)] msel_ssel_expr_load_rexp_gas(3)[OF Some(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct1] unfolding Qe_def by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>) \<longrightarrow>
              (\<forall>ev. Address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> state.Gas st' \<and>
                     Type (acc ad) = Some (atype.Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>Gas := state.Gas st0 - cc\<rparr>) (state.Gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt b256) v = Some v' \<and>
                     transfer (Address ev) ad v' (Accounts st0) = Some acc \<and>
                     iv (Storage st0 ad) (\<lceil>Bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore
                      (st0\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::state
            assume l0: "state.Gas st' < state.Gas (st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(4)[OF Some(9)] msel_ssel_expr_load_rexp_gas(3)[OF Some(2)] msel_ssel_expr_load_rexp_gas(3)[OF Some(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed
          ultimately show ?thesis using safeStore[of e\<^sub>l0 ad "st\<lparr>Gas := g0'', Accounts := acc0, Stack := k\<^sub>l0, Memory := m\<^sub>l0\<rparr>" iv f0 cd\<^sub>l0 st0''] Some unfolding Qe_def Qfe_def by blast
        qed
        ultimately show ?thesis by simp
      next
        case (None adv0 c0 g0 ct0 cn0 fb0' v0 t0 g0' v0' acc0 st0'')
        moreover have "iv (Storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts s'''''' ad)))"
        proof -
          from None have "adv0 \<noteq> ad" using a0 by auto
          then have "Address (ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)) \<noteq> ad" using ffold_init_ad_same[where ?e="\<lparr>Address = adv0, Contract = c0, Sender = Address ev, Svalue = v0', Denvalue = {$$}\<rparr>" and e'="ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)"] unfolding emptyEnv_def by simp
          moreover have "Type (Accounts (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad) = Some (atype.Contract cname)" using transfer_type_same[OF None(9)] a00 by simp
          moreover have "iv (Storage (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad)))"
          proof -
            from None(5) have "c0 |\<in>| fmdom ep" by (rule fmdomI)
            with a0 a1 None `adv0 \<noteq> ad` have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by simp
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF None(9)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<longrightarrow>
              (\<forall>mid fp f ev.
                members $$ mid = Some (Method (fp, True, f)) \<and>
                Address ev \<noteq> ad
               \<longrightarrow> (\<forall>adex cd st0 xe val g v t g' v' e\<^sub>l cd\<^sub>l k\<^sub>l' m\<^sub>l' g'' acc.
                     g'' \<le> state.Gas st' \<and>
                     Type (acc ad) = Some (atype.Contract cname) \<and>
                     local.expr adex ev cd (st0\<lparr>Gas := state.Gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>) (state.Gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g) \<and>
                     local.expr val ev cd (st0\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt b256) v = Some v' \<and>
                     local.load True fp xe (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore emptyStore emptyTypedStore ev cd (st0\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l', m\<^sub>l'), g'') \<and>
                     transfer (Address ev) ad v' (Accounts (st0\<lparr>Gas := g''\<rparr>)) = Some acc \<and>
                     iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')
                    \<longrightarrow>  wpS f (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l', Memory := m\<^sub>l'\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::state
            assume "state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF None(2)] msel_ssel_expr_load_rexp_gas(3)[OF None(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct1] unfolding Qe_def by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<longrightarrow>
              (\<forall>ev. Address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> state.Gas st' \<and>
                     Type (acc ad) = Some (atype.Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>Gas := state.Gas st0 - cc\<rparr>) (state.Gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt b256) v = Some v' \<and>
                     transfer (Address ev) ad v' (Accounts st0) = Some acc \<and>
                     iv (Storage st0 ad) (\<lceil>Bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore
                      (st0\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::state
            assume l0: "state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF None(2)] msel_ssel_expr_load_rexp_gas(3)[OF None(6)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed                                                                                                                                                                                                                                                                                                            
          ultimately have "iv (Storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st0'' ad)))" using safeStore[of "ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)" ad "st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>" iv fb0' emptyTypedStore "st0''"] None unfolding Qe_def Qfe_def by blast
          then show ?thesis using None(11) by simp
        qed
        ultimately show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (EXTERNAL ad' i xe val) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using ex.nchotomy by simp
    qed
  next
    fix ev ex ad' cd
    assume a00: "Type (Accounts st ad) = Some (atype.Contract cname)"
      and a0: "Address ev = ad"
      and a1: "\<forall>adv g. local.expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<longrightarrow> adv \<noteq> ad"
      and a2: "\<forall>adv g v t g' v'.
          local.expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
          adv \<noteq> ad \<and>
          local.expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
          convert t (TUInt b256) v = Some v' \<longrightarrow>
          iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    show "wpS (TRANSFER ad' ex) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a s''''''
      assume "x1 = (x1a, s'''''')" and "local.stmt (TRANSFER ad' ex) ev cd st = Normal x1"
      then have 2: "local.stmt (TRANSFER ad' ex) ev cd st = Normal (x1a, s'''''')" by simp
      then show "iv (Storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts s'''''' ad)))"
      proof (cases rule: transfer)
        case (Contract v0 t0 g0 adv0 c0 g0' v0' acc0 ct0 cn0 f0 st0'')
        moreover have "iv (Storage s'''''' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts s'''''' ad)))"
        proof -
          from Contract have "adv0 \<noteq> ad" using a1 by auto
          then have "Address (ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)) \<noteq> ad" using a0 ffold_init_ad_same[where ?e'="ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)"] unfolding emptyEnv_def by simp
          moreover have "Type (Accounts (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad) = Some (atype.Contract cname)" using transfer_type_same[OF Contract(7)] a00 by simp
          moreover have "iv (Storage (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) ad)))"
          proof -
            from a0 a2 Contract `adv0 \<noteq> ad` have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by blast
            moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF Contract(7)] a0 `adv0 \<noteq> ad` by simp
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<longrightarrow> Qe ad iv st'"
          proof (rule allI,rule impI)
            fix st'::state
            assume "state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by auto
            then show "Qe ad iv st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct1] by simp
          qed
          moreover have "\<forall>st'::state. state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) \<longrightarrow>
              (\<forall>ev. Address ev \<noteq> ad
               \<longrightarrow> (\<forall>ex cd st0 adex cc v t g g' v' acc.
                     g' \<le> state.Gas st' \<and>
                     Type (acc ad) = Some (atype.Contract cname) \<and>
                     expr adex ev cd (st0\<lparr>Gas := state.Gas st0 - cc\<rparr>) (state.Gas st0 - cc) = Normal ((KValue ad, Value TAddr), g) \<and>
                     expr ex ev cd (st0\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
                     convert t (TUInt b256) v = Some v' \<and>
                     transfer (Address ev) ad v' (Accounts st0) = Some acc \<and>
                     iv (Storage st0 ad) (\<lceil>Bal (acc ad)\<rceil> - \<lceil>v'\<rceil>) \<longrightarrow>
                     wpS fb (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
                      (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members)) emptyTypedStore
                      (st0\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)))" (is "\<forall>st'. ?left st' \<longrightarrow> ?right st'")
          proof (rule allI,rule impI)
            fix st'::state
            assume l0: "state.Gas st' < state.Gas (st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)"
            then have "state.Gas st' < state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by auto
            then show "?right st'" using assm[OF all_gas_le[OF `state.Gas st' < state.Gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct2] unfolding Qfe_def by simp
          qed
          ultimately have "iv (Storage st0'' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st0'' ad)))" using safeStore[of "ffold (init ct0) (emptyEnv adv0 c0 (Address ev) v0') (fmdom ct0)" ad "st\<lparr>Gas := g0', Accounts := acc0, Stack := emptyStore, Memory := emptyTypedStore\<rparr>" iv f0 emptyTypedStore "st0''"] Contract unfolding Qe_def Qfe_def by blast
          then show ?thesis using Contract(9) by simp
        qed
        ultimately show ?thesis by simp
      next
        case (EOA v0 t0 g0 adv0 g0' v0' acc0)
        moreover have "iv (Storage (st\<lparr>Gas := g0', Accounts := acc0\<rparr>) ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g0', Accounts := acc0\<rparr>) ad)))"
        proof -
          from EOA have "adv0 \<noteq> ad" using a1 by auto
          with a0 a2 EOA have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0')" by blast
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc0 ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v0'" using transfer_sub[OF EOA(6)] a0 `adv0 \<noteq> ad` by simp
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (TRANSFER ad' ex) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using ex.nchotomy by simp
    qed
  next
    fix ev i xe cd fp
    assume a0: "Type (Accounts st ad) = Some (atype.Contract cname)"
       and ad_ev: "Address ev = ad"
       and a1: "Contract ev = cname"
       and pre: "\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
          local.load False fp xe (ffold (init members) (emptyEnv ad (Contract ev) (Sender ev) (Svalue ev)) (fmdom members)) emptyTypedStore emptyStore (Memory st) ev cd (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) (state.Gas st - costs (INVOKE i xe) ev cd st) =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g) \<longrightarrow>
          pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)"
    show "wpS (INVOKE i xe) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a st'
      assume "x1 = (x1a, st')"
         and *: "local.stmt (INVOKE i xe) ev cd st = Normal x1"
      then have "local.stmt (INVOKE i xe) ev cd st = Normal (x1a, st')" by simp
      then show "post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)), Storage st' ad)"
      proof (cases rule: invoke)
        case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
        have "post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)), Storage st' ad)"
        proof -
          from * have "state.Gas st > costs (INVOKE i xe) ev cd st" by (simp add:stmt.simps split:if_split_asm)
          then have "state.Gas (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) < state.Gas st" using invoke_not_zero[of i xe ev cd st] by simp

          from a1 have "ct = members" using 1(2) C1 by simp
          then have **: "local.load False fp xe (ffold (init members) (emptyEnv ad (Contract ev) (Sender ev) (Svalue ev)) (fmdom members)) emptyTypedStore
          emptyStore (Memory st) ev cd (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>)
          (state.Gas st - costs (INVOKE i xe) ev cd st) =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)" using 1(4) ad_ev by simp
          moreover from 1(2,3) have ***: "members $$ i = Some (Method (fp, False, f))" using ad_ev `ct = members` by simp
          ultimately have "pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l)" using pre by blast
          moreover have "g \<le> state.Gas (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>)" using msel_ssel_expr_load_rexp_gas(4)[OF 1(4),THEN conjunct1] by simp
          ultimately have "wpS f (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
            (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using assm[OF all_gas_le[OF `state.Gas (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) < state.Gas st` "1.IH"], THEN conjunct2, THEN conjunct1] ** *** ad_ev a1 unfolding Qi_def by simp
          then show ?thesis unfolding wpS_def wp_def using 1(5,6) by simp
        qed
        then show ?thesis by simp
      qed
    next
      fix e
      assume "local.stmt (INVOKE i xe) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using ex.nchotomy by simp
    qed
  next
    fix ev ex ad' cd
    assume a0: "Type (Accounts st ad) = Some (atype.Contract cname)"
      and ad_ev: "Address ev = ad"
      and a1: "\<forall>adv g.
          local.expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)
           (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<longrightarrow> adv = ad"
      and a2: "\<forall>g v t g'.
          local.expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)
           (state.Gas st - costs (TRANSFER ad' ex) ev cd st) =
          Normal ((KValue ad, Value TAddr), g) \<and>
          local.expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<longrightarrow>
          pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)"
    show "wpS (TRANSFER ad' ex) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st"
      unfolding wpS_def wp_def
    proof (split result.split; split prod.split; rule conjI; (rule allI)+; (rule impI)+)
      fix x1 x1a st'
      assume "x1 = (x1a, st')" and "local.stmt (TRANSFER ad' ex) ev cd st = Normal x1"
      then have 2: "local.stmt (TRANSFER ad' ex) ev cd st = Normal (x1a, st')" by simp
      then show "postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)), Storage st' ad)"
      proof (cases rule: transfer)
        case (Contract v t g adv c g' v' acc ct cn f st'')
        moreover from Contract have "adv = ad" using a1 by auto
        ultimately have "pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)" using ad_ev a2 by auto
        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" using transfer_same[OF Contract(7)] `adv = ad` ad_ev by simp
        ultimately have "pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)), Storage st ad)" by simp
        moreover from a0 have "c = cname" using Contract(5) `adv = ad` by simp
        then have "ct = members" and "f = fb" using C1 Contract(6) by simp+
        moreover have "state.Gas st \<ge> costs (TRANSFER ad' ex) ev cd st" using 2 by (simp add:stmt.simps split:if_split_asm)
        then have "state.Gas (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) < state.Gas st" using transfer_not_zero[of ad' ex ev cd st] by simp
        moreover have "g' \<le> state.Gas (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>)" using msel_ssel_expr_load_rexp_gas(3)[OF Contract(2)] msel_ssel_expr_load_rexp_gas(3)[OF Contract(3)] by simp
        ultimately have "wpS fb (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err)
          (ffold (init members) (emptyEnv ad c (Address ev) v') (fmdom members)) emptyTypedStore
          (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using assm[OF all_gas_le[OF `state.Gas (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) < state.Gas st` "1.IH"], THEN conjunct2, THEN conjunct2, THEN conjunct1] ad_ev Contract `adv = ad` `c = cname` unfolding Qfi_def by blast
        with `ct = members` `f=fb` have "postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)), Storage st' ad)" unfolding wpS_def wp_def using Contract(8,9) `adv = ad` by simp
        then show ?thesis by simp
      next
        case (EOA v t g adv g' acc)
        then show ?thesis using a0 a1 by simp
      qed
    next
      fix e
      assume "local.stmt (TRANSFER ad' ex) ev cd st = Exception e"
      show "e = Gas \<or> e = Err" using ex.nchotomy by simp
    qed
  qed
qed

text \<open>
  Refined versions of @{thm[source] wp_external_invoke_transfer}.
\<close>

lemma wp_transfer_ext[rule_format]:
  assumes "Type (Accounts st ad) = Some (atype.Contract cname)"
      and "\<And>st::state. \<lbrakk>\<forall>st'::state. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "(\<forall>ev ex ad' cd.
       Address ev = ad \<and>
       (\<forall>adv g.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
        \<longrightarrow> adv \<noteq> ad) \<and>
       (\<forall>adv g v t g' v'.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt b256) v = Some v'
        \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (TRANSFER ad' ex) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"
proof -
  from wp_external_invoke_transfer have "Pfe ad iv st" using assms by blast
  then show ?thesis using Pfe_def by simp
qed

lemma wp_external[rule_format]:
  assumes "Type (Accounts st ad) = Some (atype.Contract cname)"
     and "\<And>st::state. \<lbrakk>\<forall>st'::state. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname)\<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
  shows "(\<forall>ev ad' i xe val cd.
       Address ev = ad \<and>
       (\<forall>adv c g v t g' v'.
         expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) (state.Gas st - costs (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g) \<and>
         adv \<noteq> ad \<and>
         Type (Accounts st adv) = Some (atype.Contract c) \<and>
         c |\<in>| fmdom ep \<and>
         expr val ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
         convert t (TUInt b256) v = Some v'
        \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v'))
      \<longrightarrow> wpS (EXTERNAL ad' i xe val) (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"
proof -
  from wp_external_invoke_transfer have "Pe ad iv st" using assms by blast
  then show ?thesis using Pe_def by simp
qed

lemma wp_invoke[rule_format]:
  assumes "Type (Accounts st ad) = Some (atype.Contract cname)"
      and "\<And>st::state. \<lbrakk>\<forall>st'::state. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
  shows "(\<forall>ev i xe cd.
       Address ev = ad \<and>
       Contract ev = cname \<and>
       (\<forall>fp e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g.
         load False fp xe (ffold (init members) (emptyEnv ad (Contract ev) (Sender ev) (Svalue ev)) (fmdom members)) emptyTypedStore emptyStore (Memory st) ev cd (st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) ev cd st\<rparr>) (state.Gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)
        \<longrightarrow> pre i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad, e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l))
    \<longrightarrow> wpS (INVOKE i xe) (\<lambda>st. post i (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"
proof -
  from wp_external_invoke_transfer have "Pi ad pre post st" using assms by blast
  then show ?thesis using Pi_def by simp
qed

lemma wp_transfer_int[rule_format]:
  assumes "Type (Accounts st ad) = Some (atype.Contract cname)"
      and "\<And>st::state. \<lbrakk>\<forall>st'::state. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow> Pe ad iv st' \<and> Pi ad pre post st' \<and> Pfi ad pref postf st' \<and> Pfe ad iv st'\<rbrakk>
                    \<Longrightarrow> Qe ad iv st \<and> Qi ad pre post st \<and> Qfi ad pref postf st \<and> Qfe ad iv st"
    shows "(\<forall>ev ex ad' cd.
     Address ev = ad \<and>
     (\<forall>adv g.
       expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)
      \<longrightarrow> adv = ad) \<and>
     (\<forall>g v t g'.
       expr ad' ev cd (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad' ex) ev cd st\<rparr>) (state.Gas st - costs (TRANSFER ad' ex) ev cd st) = Normal ((KValue ad, Value TAddr), g) \<and>
       expr ex ev cd (st\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g')
      \<longrightarrow> pref (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad))
    \<longrightarrow> wpS (TRANSFER ad' ex) (\<lambda>st. postf (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)), Storage st ad)) (\<lambda>e. e = Gas \<or> e = Err) ev cd st)"
proof -
  from wp_external_invoke_transfer have "Pfi ad pref postf st" using assms by blast
  then show ?thesis using Pfi_def by simp
qed

definition constructor :: "((String.literal, String.literal) fmap \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> bool"
  where "constructor iv \<equiv> (\<forall>acc g'' m\<^sub>l k\<^sub>l cd\<^sub>l e\<^sub>l g' t v v' xe i cd val st ev adv st0.
    st0 = st\<lparr>Gas := state.Gas st - costs (NEW i xe val) ev cd st\<rparr> \<and>
    adv = hash_version (Address ev) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts st0 (Address ev)))) \<and>
    Type (Accounts st0 adv) = None \<and>
    expr val ev cd st0 (state.Gas st0) = Normal ((KValue v, Value t), g') \<and>
    convert t (TUInt b256) v = Some v' \<and>
    load True (fst const) xe (ffold (init members) (emptyEnv adv cname (Address ev) v') (fmdom members)) emptyTypedStore emptyStore emptyTypedStore ev cd (st0\<lparr>Gas := g', Accounts := (Accounts st0)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract cname), Contracts = 0\<rparr>), Storage:=(Storage st0)(adv := {$$})\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'') \<and>
    transfer (Address ev) adv v' ((Accounts st0)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract cname), Contracts = 0\<rparr>)) = Some acc
    \<longrightarrow> wpS (snd const) (\<lambda>st. iv (Storage st adv) \<lceil>Bal (Accounts st adv)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
        (st0\<lparr>Gas := g'', Storage:=(Storage st0)(adv := {$$}), Accounts := acc, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>))"

lemma invariant_rec:
  fixes iv ad
  assumes "\<forall>ad (st::state). Qe ad iv st"
      and "\<forall>ad (st::state). Qfe ad iv st"
      and "constructor iv"
      and "Address ev \<noteq> ad"
      and "Type (Accounts st ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))"
    shows "\<forall>(st'::state). stmt f ev cd st = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname)
            \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
  using assms(4-)
proof (induction rule:stmt.induct)
  case (1 ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt SKIP ev cd st = Normal ((), st')"
       and "Type (Accounts st' ad) = Some (atype.Contract cname)"
    then show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>" using 1 skip[OF *] by simp
  qed
next
  case (2 lv ex ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt (ASSIGN lv ex) ev cd st = Normal ((), st')"
       and "Type (Accounts st' ad) = Some (atype.Contract cname)"
    then show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>" using 2 by (cases rule: assign[OF *];simp)
  qed
next
  case (3 s1 s2 ev cd st)
  show ?case
  proof elims
    fix st'
    assume *: "stmt (COMP s1 s2) ev cd st = Normal ((), st')"
       and **: "Type (Accounts st' ad) = Some (atype.Contract cname)"
      show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule: comp[OF *])
      case (1 st'')
      moreover from 3(4) have "Type (Accounts (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad) \<lceil>Bal (Accounts (st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) ev cd st\<rparr>) ad)\<rceil>" by auto
      ultimately have "Type (Accounts st'' ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st'' ad) \<lceil>Bal (Accounts st'' ad)\<rceil>" using 3(1)[OF _ _ 3(3)] by fastforce
      then show ?thesis using 3(2)[OF _ _ _ 3(3)] 1 ** by fastforce
    qed
  qed
next
  case (4 ex s1 s2 ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (ITE ex s1 s2) ev cd st = Normal ((), st')"
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
      show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:ite[OF a1])
      case (1 g)
      have "\<forall>st'. local.stmt s1 ev cd (st\<lparr>Gas := g\<rparr>) = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
        apply (rule 4(1)) using 1 4(3) 4(4) by auto
      then show ?thesis using a2 1(3) by blast
    next
      case (2 g)
      have "\<forall>st'. local.stmt s2 ev cd (st\<lparr>Gas := g\<rparr>) = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
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
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
      show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:while[OF a1])
      case (1 g st'')
      have "\<forall>st'. local.stmt s0 ev cd (st\<lparr>Gas := g\<rparr>) = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
        apply (rule 5(1)) using 1 5(3) 5(4) by auto
      then have *: "Type (Accounts st'' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st'' ad) \<lceil>Bal (Accounts st'' ad)\<rceil>" using 1(3) by simp
      have "\<forall>st'. local.stmt (WHILE ex s0) ev cd st'' = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
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
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:invoke[OF a1])
      case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
      from 6(2) have "ad \<noteq> Address e\<^sub>l" using msel_ssel_expr_load_rexp_gas(4)[OF 1(4)] ffold_init_ad by simp
      have "\<forall>st'. local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>" apply (rule 6(1)) using 1 6(3) `ad \<noteq> Address e\<^sub>l` by auto
      then show ?thesis using a2 1(5,6) by auto
    qed
  qed
next
  case (7 adex i xe val ev cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (EXTERNAL adex i xe val) ev cd st = Normal ((), st')"
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:external[OF a1])
      case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "Type (acc ad) = Some (atype.Contract c)" using transfer_type_same[OF 1(10)] 1(4) by auto
        moreover from `Type (acc ad) = Some (atype.Contract c)` have "Type (Accounts st' ad) = Some (atype.Contract c)" using atype_same[OF 1(11)] 1(12) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" using 1 C1 by simp
        moreover have "g'' \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(6)] msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] by linarith
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "Type (Accounts st ad) = Some (atype.Contract cname)" using 1(4) True by simp
          have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using 7(4) `Type (Accounts st ad) = Some (atype.Contract cname)` by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(10)] 7(3) True by simp
          ultimately show ?thesis by simp
        qed
        ultimately have "wpS f (\<lambda>st. iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
        (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)" using 1 True  using assms(1) 1(8) 7(3) unfolding Qe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 1(11,12) by simp
      next
        case False
        then have *: "ad \<noteq> Address e\<^sub>l" using msel_ssel_expr_load_rexp_gas(4)[OF 1(9)] ffold_init_ad by simp
        moreover have **:"Type (acc ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>"
        proof
          assume "Type (acc ad) = Some (atype.Contract cname)"
          then have "Type (Accounts st ad) = Some (atype.Contract cname)" using transfer_type_same[OF 1(10)] by simp
          then have "iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>" using 7(4) by simp
          moreover have "Bal (acc ad) = Bal (Accounts st ad)" using transfer_eq[OF 1(10)] 7(3) False by simp
          ultimately show "iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt f e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st') \<and>
         Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>  iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
          using 7(1) 1 by auto
        then show ?thesis using a2 1(11,12) by simp
      qed
    next
      case (2 adv c g ct cn fb' v t g' v' acc st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "Type (acc ad) = Some (atype.Contract c)" using transfer_type_same[OF 2(9)] 2(4) by auto
        moreover from `Type (acc ad) = Some (atype.Contract c)` have "Type (Accounts st' ad) = Some (atype.Contract c)" using atype_same[OF 2(10)] 2(11) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" and "fb'=fb" using 2 C1 by simp+
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "Type (Accounts st ad) = Some (atype.Contract cname)" using 2(4) True by simp
          then have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using 7(4) by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 2(9)] 7(3) True by simp
          ultimately show "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')" by simp
        qed
        moreover have "g' \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 2(2)] msel_ssel_expr_load_rexp_gas(3)[OF 2(6)] by linarith
        ultimately have "wpS fb' (\<lambda>st. iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
          (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore
          (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using assms(2) 7(3) 2 True unfolding Qfe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 2(10,11) by simp
      next
        case False
        moreover have **:"Type (acc ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>"
        proof
          assume "Type (acc ad) = Some (atype.Contract cname)"
          then have "Type (Accounts st ad) = Some (atype.Contract cname)" using transfer_type_same[OF 2(9)] by simp
          then have "iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>" using 7(4) by simp
          moreover have "Bal (acc ad) = Bal (Accounts st ad)" using transfer_eq[OF 2(9)] 7(3) False by simp
          ultimately show "iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt fb' (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st') \<and>
         Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>  iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
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
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:transfer[OF a1])
      case (1 v t g adv c g' v' acc ct cn f st'')
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then have "Type (acc ad) = Some (atype.Contract c)" using transfer_type_same[OF 1(7)] 1(5) by auto
        moreover from `Type (acc ad) = Some (atype.Contract c)` have "Type (Accounts st' ad) = Some (atype.Contract c)" using atype_same[OF 1(8)] 1(9) by simp
        then have "c = cname" using a2 by simp
        moreover from `c = cname` have "ct = members" and "f=fb" using 1 C1 by simp+
        moreover have "g' \<le> state.Gas st" using msel_ssel_expr_load_rexp_gas(3)[OF 1(2)] msel_ssel_expr_load_rexp_gas(3)[OF 1(3)] by linarith
        moreover have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
        proof -
          from `c = cname` have "Type (Accounts st ad) = Some (atype.Contract cname)" using 1(5) True by simp
          then have "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))" using 8(3) by simp
          moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v'" using transfer_add[OF 1(7)] 8(2) True by simp
          ultimately show "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')" by simp
        qed
        ultimately have "wpS f (\<lambda>st. iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err)
          (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore
          (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" using assms(2) 8(2) 1 True unfolding Qfe_def by simp
        then show ?thesis unfolding wpS_def wp_def using 1(8,9) by simp
      next
        case False
        moreover have "Type (acc ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>"
        proof
          assume "Type (acc ad) = Some (atype.Contract cname)"
          then have "Type (Accounts st ad) = Some (atype.Contract cname)" using transfer_type_same[OF 1(7)] by simp
          then have "iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>" using 8(3) by simp
          moreover have "Bal (acc ad) = Bal (Accounts st ad)" using transfer_eq[OF 1(7)] 8(2) False by simp
          ultimately show "iv (Storage st ad) \<lceil>Bal (acc ad)\<rceil>" by simp
        qed
        ultimately have "\<forall>st'. local.stmt f (ffold (init ct) (emptyEnv adv c (Address ev) v') (fmdom ct)) emptyTypedStore
          (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>" using 8(1) 1 by auto
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
        then have "Bal (acc ad) = Bal (Accounts st ad)" using transfer_eq[OF 2(6)] 8(2) by simp
        moreover have "Type (Accounts st ad) = Some (atype.Contract cname)" using transfer_type_same[OF 2(6)] 2(7) a2 by simp
        then have "iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>" using 8(3) by simp
        ultimately show ?thesis using 2(7) by simp
      qed
    qed
  qed
next
  case (9 id0 tp s e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (BLOCK (id0, tp, None) s) e cd st = Normal ((), st')"
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:blockNone[OF a1])
      case (1 cd' mem' sck' e')
      have "Address e' = Address e" using decl_env[OF 1(2)] by simp
      have "\<forall>st'. local.stmt s e' cd' (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e cd st, Stack := sck',
           Memory := mem'\<rparr>) = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
        apply (rule 9(1)) using 1 9(2,3) `Address e' = Address e` by auto
      then show ?thesis using a2 1(3) by blast
    qed
  qed
next
  case (10 id0 tp ex' s e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (BLOCK (id0, tp, Some ex') s) e cd st = Normal ((), st')"
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:blockSome[OF a1])
      case (1 v t g cd' mem' sck' e')
      have "Address e' = Address e" using decl_env[OF 1(3)] by simp
      have "\<forall>st'. local.stmt s e' cd' (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) = Normal ((), st') \<and>
          Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow>
          iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
        apply (rule 10(1)) using 1 10(2,3) `Address e' = Address e` by auto
      then show ?thesis using a2 1(4) by blast
    qed
  qed
next
  case (11 i xe val e cd st)
  show ?case
  proof elims
    fix st'
    assume a1: "local.stmt (NEW i xe val) e cd st = Normal ((), st')"
       and a2: "Type (Accounts st' ad) = Some (atype.Contract cname)"
    show "iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
    proof (cases rule:new[OF a1])
      case (1 v t g ct cn fb' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'' v')
      define adv where "adv = hash_version (Address e) \<lfloor>Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e))\<rfloor>"
      then have "Address e\<^sub>l = adv" using msel_ssel_expr_load_rexp_gas(4)[OF 1(6)] by simp
      then show ?thesis
      proof (cases "adv = ad")
        case True
        then show ?thesis
        proof (cases "i = cname")
          case t0: True
          then have "ct = members" and "cn = const" and "fb' = fb" using 1(5) C1 by simp+
          then have "wpS (snd const) (\<lambda>st. iv (Storage st adv) \<lceil>Bal (Accounts st adv)\<rceil>) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
            (st\<lparr>Gas := g', Storage:=(Storage st)(adv := {$$}), Accounts := acc, Stack:=k\<^sub>l, Memory:=m\<^sub>l\<rparr>)"
            using assms(3) 11(3) 1 True adv_def t0 unfolding constructor_def by auto
          then have "iv (Storage st'' adv) \<lceil>Bal (Accounts st'' adv)\<rceil>" unfolding wpS_def wp_def using 1(8) `cn = const` adv_def by simp
          then show ?thesis using 1(9) True by simp
        next
          case False
          moreover have "Type (Accounts st' ad) = Some (atype.Contract i)"
          proof -
            from `adv = ad` have "Type (((Accounts st) (adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>)) ad) = Some (atype.Contract i)" by simp
            then have "Type (acc ad) = Some (atype.Contract i)" using transfer_type_same[OF 1(7)] adv_def by simp
            then have "Type (Accounts st'' ad) = Some (atype.Contract i)" using atype_same[OF 1(8)] adv_def by simp
            then show ?thesis using 1(9) by simp
          qed
          ultimately show ?thesis using a2 by simp
        qed
      next
        case False
        define st0 where "st0 = st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>"
        define st1 where "st1 = st\<lparr>Gas := g, Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (Storage st)(adv := {$$})\<rparr>"
        define st2 where "st2 = st1\<lparr>Gas := g'\<rparr>"
        define st3 where "st3 = st2\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>"

        have aux1: "Type (acc ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage (st\<lparr>Storage:=(Storage st)(adv := {$$}), Accounts:=acc\<rparr>) ad) \<lceil>Bal (acc ad)\<rceil>"
        proof
          assume "Type (acc ad) = Some (atype.Contract cname)"
          then have "Type (((Accounts st) (adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>)) ad) = Some (atype.Contract cname)"
            using transfer_type_same[OF 1(7)] adv_def by simp
          then have "Type ((Accounts st) ad) = Some (atype.Contract cname)" using False by simp
          then have "iv (Storage st ad) \<lceil>Bal (Accounts st ad)\<rceil>" using 11(3) by simp
          then have "iv (Storage (st\<lparr>Storage:=(Storage st)(adv := {$$})\<rparr>) ad) \<lceil>Bal (Accounts st ad)\<rceil>" using False by simp
          then show "iv (Storage (st\<lparr>Storage:=(Storage st)(adv := {$$}), Accounts:=acc\<rparr>) ad) \<lceil>Bal (acc ad)\<rceil>"
            using transfer_eq[OF 1(7)] adv_def 11(2) False by simp
        qed

        have b1: "assert Gas (\<lambda>st. costs (NEW i xe val) e cd st < state.Gas st) st = Normal ((), st)" using 1(1) by simp
        have b2: "modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) st = Normal ((), st0)" using st0_def by simp
        have b3: "applyf (\<lambda>st. hash_version (Address e) \<lfloor>Contracts (Accounts st (Address e))\<rfloor>) st0 = Normal (adv, st0)" using adv_def st0_def by simp
        have b4: "assert Err (\<lambda>st. Type (Accounts st adv) = None) st0 = Normal ((), st0)" using 1(2) st0_def adv_def by simp
        have b5: "toState (expr val e cd) st0 = Normal ((KValue v, Value t), st0\<lparr>Gas := g\<rparr>)" using 1(3) st0_def by simp
        have b6: "(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | _ \<Rightarrow> throw Err) (st0\<lparr>Gas := g\<rparr>) = Normal ((v, t), st0\<lparr>Gas := g\<rparr>)" by simp
        then have b7: "return (v, t) (st0\<lparr>Gas := g\<rparr>) = Normal ((v, t), st0\<lparr>Gas := g\<rparr>)" by simp
        have b8: "option Err (\<lambda>_. convert t (TUInt b256) v) (st0\<lparr>Gas := g\<rparr>) = Normal (v', st0\<lparr>Gas := g\<rparr>)" using 1(4) by simp
        have b9: "option Err (\<lambda>_. ep $$ i) (st0\<lparr>Gas := g\<rparr>) = Normal ((ct, cn, fb'), st0\<lparr>Gas := g\<rparr>)" using 1(5) by simp
        have b10: "modify (\<lambda>st. st\<lparr>Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (Storage st)(adv := {$$})\<rparr>) (st0\<lparr>Gas := g\<rparr>) = Normal ((), st1)" using st1_def st0_def by simp
        have b11: "toState
     (local.load True (fst cn) xe (ffold_init ct (emptyEnv adv i (Address e) v') (fmdom ct)) emptyTypedStore emptyStore
       emptyTypedStore e cd)
     st1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), st2)" using 1(6) st1_def st2_def st0_def adv_def by simp
        have b12: "option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) st2 = Normal (acc, st2)" using 1(7) st2_def st1_def st0_def adv_def by simp
        have b13: "applyf (\<lambda>st. (Stack st, Memory st)) st2 = Normal ((Stack st, Memory st), st2)" 
          using st1_def st2_def by auto
        have b14: "modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) st2 = Normal ((), st3)" using st3_def by simp

        (* Show st3 equals the state where stmt is executed in 1(8) *)
        have st3_eq: "st3 = st\<lparr>Gas := g', Accounts := (Accounts st)(adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), Storage := (Storage st)(adv := {$$}), Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>"
          using st3_def st2_def st1_def by simp

        have "Address e\<^sub>l \<noteq> ad" using `Address e\<^sub>l = adv` False by simp
        moreover have "Type (Accounts st3 ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st3 ad) \<lceil>Bal (Accounts st3 ad)\<rceil>"
          using aux1 st3_def st2_def st1_def st0_def by simp
        ultimately have stmt_ih: "\<forall>st'. stmt (snd cn) e\<^sub>l cd\<^sub>l st3 = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st' ad) \<lceil>Bal (Accounts st' ad)\<rceil>"
          using 11(1)[OF b1 b2 b3 b4 b5 b6 refl b8 b9 refl refl b10 refl b11 refl refl refl b12 b13 refl b14] by blast

        (* Now use st3_eq to connect to 1(8) *)
        have "stmt (snd cn) e\<^sub>l cd\<^sub>l st3 = Normal ((), st'')" using 1(8) st3_eq 
          using adv_def by fastforce
        moreover have "Type (Accounts st'' ad) = Some (atype.Contract cname)" using 1(9) a2 adv_def by auto
        ultimately show ?thesis using stmt_ih 1(9) by simp
      qed
    qed
  qed
qed

theorem invariant:
  fixes iv ad
  assumes "\<forall>ad (st::state). Qe ad iv st"
      and "\<forall>ad (st::state). Qfe ad iv st"
      and "constructor iv"
      and "\<forall>ad. Type (Accounts st ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))"
    shows "\<forall>(st'::state) ad. stmt f ev cd st = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<and> Address ev \<noteq> ad
            \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
  using assms invariant_rec by blast
end

context Calculus
begin

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
    rule cases,
    simp
  
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
  
  method vcg_assign uses wp_rule expr_rule lexp_rule =
    rule wp_rule,
    simp add: expr_rule lexp_rule,
    simp

  subsection \<open>Composition\<close>
  
  method vcg_comp =
    rule wp_Comp; simp

  subsection \<open>Blocks\<close>
  
  method vcg_block_some =
    rule wp_blockSome; simp
end

locale VCG = Calculus +
  fixes iv::invariant
    and pref::"postcondition"
    and postf::"postcondition"
    and pre::"Identifier \<Rightarrow> precondition"
    and post::"Identifier \<Rightarrow> postcondition"
begin

subsection \<open>Transfer\<close>
text \<open>
  The following rule can be used to verify an invariant for a transfer statement.
  It requires four term parameters:
  \<^item> @{term[show_types] "iv::invariant"}: Invariant
  \<^item> @{term[show_types] "pref::postcondition"}: Precondition for fallback method called internally
  \<^item> @{term[show_types] "postf::postcondition"}: Postcondition for fallback method called internally
  \<^item> @{term[show_types] "pre::Identifier \<Rightarrow> precondition"}: Preconditions for internal methods
  \<^item> @{term[show_types] "post::Identifier \<Rightarrow> postcondition"}: Postconditions for internal methods


  In addition it requires 8 facts:
  \<^item> @{term fallback_int}: verifies *postcondition* for body of fallback method invoked *internally*.
  \<^item> @{term fallback_ext}: verifies *invariant* for body of fallback method invoked *externally*.
  \<^item> @{term cases_ext}: performs case distinction over *external* methods of atype.Contract @{term ad}.
  \<^item> @{term cases_int}: performs case distinction over *internal* methods of atype.Contract @{term ad}.
  \<^item> @{term cases_fb}: performs case distinction over *fallback* method of atype.Contract @{term ad}.
  \<^item> @{term different}: shows that Address of environment is different from @{term ad}.
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
        (simp,vcg_prep,
         rule external;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qi _ _ _ _" \<Rightarrow>
      \<open>unfold Qi_def,
       vcg_prep,
       erule cases_int;
        (simp,vcg_prep,
         rule internal;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qfi _ _ _ _" \<Rightarrow>
      \<open>unfold Qfi_def,
       rule allI,
       rule impI,
       rule cases_fb;
        (simp,vcg_prep,
         rule fallback_int;
           solve \<open>assumption | simp\<close>)\<close>
  \<bar> "Qfe _ _ _" \<Rightarrow>
      \<open>unfold Qfe_def,
       rule allI,
       rule impI,
       rule cases_fb;
        (simp,vcg_prep,
         rule fallback_ext;
           solve \<open>assumption | simp\<close>)\<close>

method decl_load_rec for ad::address and e::environment uses eq decl load empty init =
  match premises in
    d: "decl _ _ _ _ _ _ _ (_, _, _, e') = Some (_, _, _, e)" for e'::environment \<Rightarrow>
        \<open>decl_load_rec ad e' eq:trans_sym[OF eq decl[OF d]] decl:decl load:load empty:empty init:init\<close>
  \<bar> l: "load _ _ _ (ffold (init members) (emptyEnv ad cname (Address e') v) (fmdom members)) _ _ _ _ _ _ _ = Normal ((e, _, _, _), _)" for e'::environment and v \<Rightarrow>
        \<open>rule
          trans[
            OF eq
            trans[
              OF load[OF l]
              trans[
                OF init[of (unchecked) members "emptyEnv ad cname (Address e') v" "fmdom members"]
                empty[of (unchecked) ad cname "Address e'" v]]]]\<close>

method sameaddr for ad::address =
  match conclusion in
    "Address e = ad" for e::environment \<Rightarrow>
      \<open>decl_load_rec ad e eq:refl[of "Address e"] decl:decl_env[THEN conjunct1] load:msel_ssel_expr_load_rexp_gas(4)[THEN conjunct2, THEN conjunct1] init:ffold_init_ad empty:emptyEnv_address\<close>

lemma eq_neq_eq_imp_neq:
  "x = a \<Longrightarrow> b \<noteq> y \<Longrightarrow> a = b \<Longrightarrow> x \<noteq> y" by simp

method sender for ad::address =
  match conclusion in
    "adv \<noteq> ad" for adv::address \<Rightarrow>
      \<open>match premises in
        a: "Address e' \<noteq> ad" and e: "expr SENDER e _ _ _ = Normal ((KValue adv, Value TAddr), _)" for e::environment and e'::environment \<Rightarrow>
          \<open>rule local.eq_neq_eq_imp_neq[OF expr_sender[OF e] a],
           decl_load_rec ad e eq:refl[of "Sender e"] decl:decl_env[THEN conjunct2, THEN conjunct1] load:msel_ssel_expr_load_rexp_gas(4)[THEN conjunct2, THEN conjunct2, THEN conjunct1] init:ffold_init_sender empty:emptyEnv_sender\<close>\<close>

method vcg_init for ad::address uses invariant =
  elims,
  sameaddr ad,
  sender ad,
  (rule invariant; assumption)

method vcg_transfer_ext for ad::address
  uses fallback_int fallback_ext cases_ext cases_int cases_fb invariant =
  rule wp_transfer_ext[where pref = pref and postf = postf and pre = pre and post = post and iv=iv],
  solve simp,
  (vcg_body fallback_int:fallback_int fallback_ext:fallback_ext cases_ext:cases_ext cases_int:cases_int cases_fb:cases_fb)+,
  vcg_init ad invariant:invariant

end

end