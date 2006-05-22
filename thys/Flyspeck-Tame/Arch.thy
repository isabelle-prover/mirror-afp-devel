(*  ID:         $Id: Arch.thy,v 1.1 2006-05-22 09:53:58 nipkow Exp $
    Author:     Tobias Nipkow
*)

header "Archive"

theory Arch
imports Main
uses ("arch.ML")
 ("Archives/Tri.ML")
 ("Archives/Quad.ML")
 ("Archives/Pent.ML")
 ("Archives/Hex.ML")
 ("Archives/Hept.ML")
 ("Archives/Oct.ML")
begin

text{* The Archive is contained in 6 ML files. *}

use "Archives/Tri.ML"
use "Archives/Quad.ML"
use "Archives/Pent.ML"
use "Archives/Hex.ML"
use "Archives/Hept.ML"
use "Archives/Oct.ML"

use "arch.ML"
setup {* add_archconstdefs *}

text{* First the ML values are loaded. Then they are turned into
Isabelle definitions of the constants @{const Tri}, @{const Quad},
@{const Pent}, @{const Hex}, @{const Hept}, @{const Oct}, all of type
@{typ"nat list list list"}. *}

end
