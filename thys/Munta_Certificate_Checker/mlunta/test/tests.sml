fun main () =
    (
      TestInt8.check "Int8";
      TestInt32.check "Int32";
      TestInt64.check "Int64";

      TestEntry8.check "Entry8Bit";
      TestEntry32.check "Entry64Bit";
      TestEntry64.check "Entry64Bit";
      TestEntryInt.check "Int Rep";

      TestLnDBM8.check "LnDBM8Bit";
      TestLnDBM32.check "LnDBM32Bit";
      TestLnDBM64.check "LnDBM64Bit";
      TestLnDBMIntRep.check "LnDBMIntRep";

      JsonParserTest.check "Json-Parsing Units";
      ParseJsonTATest.check "JSON-Parsing-Examples";
      BexpParserTest.check "Bexp-Parsing";
      RewriteGITest.check "Compiling Guards & Invars";
      RenamingTest.check "Renaming";
      ConstraintTest.check "Constraint";
      PolyPWListTest.check "PolyPWList";

      ReachabilityTest.check "Reachability Tests";
      AlwaysEventuallyTest.check "Always Eventually Tests";
      LeadstoTest.check "Leadsto Tests"
    ) handle _ => "TESTS Failed XXX !!!\n" ^
                  "Some unhandled Exception was thrown!\n"
                  |> print
