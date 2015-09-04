(* Load extracted code *)
use "LTL_to_DRA_Translator.sml";

(* Load mlyacc libraries *)
(* Yes, this requires mlton, since mlyacc is distributed with it *)
(* TODO: Fix this, or have a more generic way to handle it *)
use "/usr/local/lib/mlton/sml/mlyacc-lib/base.sig";
use "/usr/local/lib/mlton/sml/mlyacc-lib/join.sml";
use "/usr/local/lib/mlton/sml/mlyacc-lib/lrtable.sml";
use "/usr/local/lib/mlton/sml/mlyacc-lib/stream.sml";
use "/usr/local/lib/mlton/sml/mlyacc-lib/parser2.sml";

(* Load LTL parser *)
use "ltl/datatypes.sml";
use "ltl/ltl.yacc.sig";
use "ltl/ltl.yacc.sml";
use "ltl/ltl.lex.sml";
use "ltl/glue.sml";
use "ltl/compiler.sml";

(* Load CLI Interface *)
use "LTL_to_DRA_CLI.sml";