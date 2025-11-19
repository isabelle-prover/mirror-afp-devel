(*  Title:      Zippy/alternating_zipper_path.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH"\<close> =
sig
  (*pathi is a path starting from layer 1 and stopping at layer i;
  the layer positions are stored from right to left*)
  datatype path1 = Pos of Zipper_Position.pos
    | Path1 of Zipper_Position.pos * \<^eval>\<open>"path" ^ pred_mod_nzippers 1\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  and path{i} = Path{i} of Zipper_Position.pos * path\<^eval>\<open>pred_mod_nzippers {i}\<close>
  \<close> start: 2\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  (*create path from nested list of x-positions, where x-positions and positions are stored from
  right to left.*)
  val path_from_root_rev{i} : Zipper_Position.pos list -> path{i}
  (*create path from nested list of x-positions, where x-positions and positions are stored from
  left to right.*)
  val path_from_root{i} : Zipper_Position.pos list -> path{i}\<close>\<close>
end

structure \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path"\<close>
  : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH"\<close> =
struct
datatype path1 = Pos of Zipper_Position.pos
  | Path1 of Zipper_Position.pos * \<^eval>\<open>"path" ^ pred_mod_nzippers 1\<close>
\<^imap>\<open>\<open>{i}\<close> => \<open>
and path{i} = Path{i} of Zipper_Position.pos * path\<^eval>\<open>pred_mod_nzippers {i}\<close>
\<close> start: 2\<close>

fun path_from_root_rev1 [] = error "Invalid path length."
  | path_from_root_rev1 [pos] = Pos pos
  | path_from_root_rev1 (pos :: ps) = Path1 (pos, \<^eval>\<open>"path_from_root_rev" ^ pred_mod_nzippers 1\<close> ps)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and path_from_root_rev{i} [] = error "Invalid path length."
  | path_from_root_rev{i} (pos :: ps) = Path{i} (pos, path_from_root_rev\<^eval>\<open>pred_mod_nzippers {i}\<close> ps)
\<close> start: 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
val path_from_root{i} = List.map List.rev #> List.rev #> path_from_root_rev{i}\<close>\<close>

end
