chapter \<open>An Application: Tic-Tac-Toe\<close>

theory TicTacToe
imports
  "Alpha_Beta_Pruning.Alpha_Beta_Linear"
begin

text \<open>We formalize a general nxn version of tic-tac-toe (noughts and crosses).
The winning condition is very simple: a full horizontal, vertical or diagonal line
occupied by one player.\<close>

text \<open>A square is either empty (\<open>None\<close>) or occupied by one of the two players (\<open>Some b\<close>).\<close>

type_synonym sq = "bool option"
type_synonym row = "sq list"
type_synonym position = "row list"

text \<open>Successor positions:\<close>

fun next_rows :: "sq \<Rightarrow> row \<Rightarrow> row list" where
"next_rows s' (s#ss) = (if s=None then [s'#ss] else []) @ map ((#) s) (next_rows s' ss)" |
"next_rows _ [] = []"

fun next_poss :: "sq \<Rightarrow> position \<Rightarrow> position list"  where
"next_poss s' (ss#sss) = map (\<lambda>ss'. ss' # sss) (next_rows s' ss) @ map ((#) ss) (next_poss s' sss)" |
"next_poss _ [] = []"

text \<open>A game is won if a full line is occupied by a given square:\<close>

fun diag :: "'a list list \<Rightarrow> 'a list" where
"diag ((x#_) # xss) = x # diag (map tl xss)" |
"diag [] = []"

fun lines :: "position \<Rightarrow> sq list list" where
"lines sss = diag sss # diag (map rev sss) # sss @ transpose sss"

fun won :: "sq \<Rightarrow> position \<Rightarrow> bool" where
"won sq pos = (\<exists>ss \<in> set (lines pos). \<forall>s \<in> set ss. s = sq)"

text \<open>How many lines are almost won (i.e. all \<open>sq\<close> except one \<open>None\<close>)?
Not actually used for heuristic evaluation, too slow.\<close>

fun awon :: "sq \<Rightarrow> position \<Rightarrow> nat" where
"awon sq sss = length (filter (\<lambda>ss. filter (\<lambda>s. s\<noteq>sq) ss = [None]) (lines sss))"

text \<open>The game tree up to a given depth \<open>n\<close>.
Trees at depth \<open>\<ge> n\<close> are replaced by \<open>Lf 0\<close> for simplicity; no heuristic evaluation.\<close>

fun tree :: "nat \<Rightarrow> bool \<Rightarrow> position \<Rightarrow> ereal tree" where
"tree (Suc n) b pos = (
  if won (Some (\<not>b)) pos then Lf(if b then -\<infinity> else \<infinity>) \<comment>\<open>Opponent won\<close>
  else
  case next_poss (Some b) pos of
    [] \<Rightarrow> Lf 0  \<comment>\<open>Draw\<close> |
    poss \<Rightarrow> Nd (map (tree n (\<not>b)) poss))" |
"tree 0 b pos = Lf 0"

definition start :: "nat \<Rightarrow> position" where
"start n = replicate n (replicate n None)"


text \<open>Now we evaluate the game for small \<open>n\<close>.\<close>

text \<open>The trivial cases:\<close>

lemma "maxmin (tree 2 True (start 1)) = \<infinity>"
by eval

lemma "maxmin (tree 5 True (start 2)) = \<infinity>"
by eval

text \<open>3x3, full game tree (depth=10), no noticeable speedup of alpha-beta.\<close>

lemma "maxmin (tree 10 True (start 3)) = 0"
by eval
lemma "ab_max (-\<infinity>) \<infinity> (tree 10 True (start 3)) = 0"
by eval

text \<open>4x4, game tree up to depth 7, alpha-beta noticeably faster.\<close>

lemma "maxmin (tree 7 True (start 4)) = 0"
by eval
lemma "ab_max (-\<infinity>) \<infinity> (tree 7 True (start 4)) = 0"
by eval

end
