#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified ExtractedString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Prelude
import qualified System.IO.Unsafe
import qualified GHC.Real
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;

    print;
}
