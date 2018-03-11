#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified ExtractedString as HString
import qualified GHC.Real
import qualified Prelude
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    print;
}
