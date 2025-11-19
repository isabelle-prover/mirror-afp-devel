use "src/parsing/util/build.sml";
use "src/parsing/json/build.sml";
use "src/parsing/ir_types/build.sml";

Build.subdir "src/parsing/"
             ["parse_json",  "parse_bexps", "parser"]
